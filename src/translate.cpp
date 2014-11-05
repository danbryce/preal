/*********************************************************************
Author: Dan Bryce <dbryce@sift.net>

pReal -- Copyright (C) 2014 - 2014, Dan Bryce

pReal is free software: you can redistribute it and/or modify
it under the terms of the MIT License.

pReal is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
MIT License for more details.

*********************************************************************/

#include "translate.h"
#include <glog/logging.h>
#include <gflags/gflags.h>
#include <val/ptree.h>
#include <stdlib.h>

using namespace VAL;

DEFINE_string(outfile, "out.smt2", "SMT2 output file");
DEFINE_int32(num_happenings, 0, "Number of happenings");

void translate::translateSMT(VAL::analysis* my_analysis){
  LOG(INFO) << "Translating Analysis";

  std::ofstream out((string)FLAGS_outfile);
  if(!out) LOG(ERROR) << "Could not open output file: " << FLAGS_outfile;

  problem* my_problem = my_analysis->the_problem;
  domain* my_domain   = my_analysis->the_domain;


  // Initial State
  effect_lists* my_initial_state = my_problem->initial_state;
  trans(my_analysis, my_initial_state, 0, out);


  // Goal
  goal *my_goal = my_problem->the_goal;
  out << "(or ";
  for(int i = 0; i <= FLAGS_num_happenings; i++){
    trans(my_analysis, my_goal, i, -1, out);
  }
  out << ")";

  operator_list* ops = my_domain->ops; 
 

  for(operator_list::iterator j = ops->begin(); j != ops->end(); j++){

    std::list<param_grounding*>* groundings = get_groundings(*j, list<VAL::const_symbol*> *constants);

    action *my_action;
    event *my_event;
    process *my_process;
    durative_action *my_durative_action;
    
    if( my_action = dynamic_cast<action*>(*j) ){
    } else if ( my_event = dynamic_cast<event*>(*j) ){
    } else if ( my_process = dynamic_cast<process*>(*j) ){
    } else if ( my_durative_action = dynamic_cast<durative_action*>(*j) ){
      for(std::list<param_grounding*>::iterator k = groundings
      for(int i = 0; i <= FLAGS_num_happenings; i++){
	trans(my_analysis, my_durative_action, i, out);
	
	// action continuity
	if(i < FLAGS_num_happenings){
	  out << "(imply (" << my_durative_action->name->getName() << "_start_t" << i <<")" 
	      << " (or (" << my_durative_action->name->getName() << "_cont_t" << (i+1) <<") (" << my_durative_action->name->getName() << "_end_t" << (i+1) <<")))";
	  out << "(imply (" << my_durative_action->name->getName() << "_cont_t" << i <<")" 
	      << " (or (" << my_durative_action->name->getName() << "_cont_t" << (i+1) <<") (" << my_durative_action->name->getName() << "_end_t" << (i+1) <<")))";
	} else if (i > 0){
	  out << "(imply (" << my_durative_action->name->getName() << "_end_t" << i <<")"
	      << " (or (" << my_durative_action->name->getName() << "_cont_t" << (i-1) <<") (" << my_durative_action->name->getName() << "_start_t" << (i-1) <<")))";
	  out << "(imply (" << my_durative_action->name->getName() << "_cont_t" << i <<")"
	      << " (or (" << my_durative_action->name->getName() << "_cont_t" << (i-1) <<") (" << my_durative_action->name->getName() << "_start_t" << (i-1) <<")))";
	}
      } 
      //Actions don't continue at extreme time points
      out << "(not (" << my_durative_action->name->getName() << "_cont_t0))";
      out << "(not (" << my_durative_action->name->getName() << "_cont_t" << FLAGS_num_happenings << "))";
    }

    for(std::list<param_grounding*>::iterator *i = groundings->begin(); i != groundings->end(); i++){
      delete *i;
    }
    delete groundings;
  }

  LOG(INFO) << "Finished Translating.";
  out.close();

}

std::list<param_grounding*>* translate::get_groundings(VAL::operator_ *op, list<VAL::const_symbol*> *constants){
  std::list<param_grounding*> *groundings = new std::list<param_grounding*>();
  return groundings;
}


void translate::trans(VAL::analysis* my_analysis, VAL::effect_lists *ef_lists, int tm, std::ofstream& out){
  
    ostringstream convert;
    convert << tm; 
    string time = "t" + convert.str();


  pc_list<simple_effect*> my_add_effects = ef_lists->add_effects;
  for(pc_list<simple_effect*>::iterator i = my_add_effects.begin();
      i != my_add_effects.end(); i++){
    (*i)->setWriteController((auto_ptr<WriteController>)getWriteController());
    out << "(";
    (*i)->prop->write(out);
    out << "_" << time << ")";
  }

  pc_list<simple_effect*> my_del_effects = ef_lists->del_effects;
  for(pc_list<simple_effect*>::iterator i = my_del_effects.begin();
      i != my_del_effects.end(); i++){
    (*i)->setWriteController((auto_ptr<WriteController>)getWriteController());
    out << "(not (";
    (*i)->prop->write(out);
    out << "_" << time << "))";
  }

  pc_list<assignment*> my_assign_effects = ef_lists->assign_effects;
  for(pc_list<assignment*>::iterator i = my_assign_effects.begin();
      i != my_assign_effects.end(); i++){
    (*i)->setWriteController((auto_ptr<WriteController>)getWriteController());
    if((*i)->getOp() == VAL::E_ASSIGN){
      out << "(= ";
      (*i)->getFTerm()->write(out);
      out << "_" << time << " ";
      (*i)->getExpr()->write(out);
      out << ")";
    } else {
      LOG(ERROR) << "Unhandled Assignment type in effect" << (*i)->getOp();
    }
  }


  pc_list<timed_effect*> my_timed_effects = ef_lists->timed_effects;
  for(pc_list<timed_effect*>::iterator i = my_timed_effects.begin();
      i != my_timed_effects.end(); i++){
    timed_initial_literal* til;
    if(til = dynamic_cast<timed_initial_literal*>(*i)){
      // string timepoint = getTimepoint(til->time_stamp);
      til->setWriteController((auto_ptr<WriteController>)getWriteController());
      out << "(or ";
      for(int i = 0; i <= FLAGS_num_happenings; i++){     
	ostringstream convert;
	convert << i; 
	string tilTime = "t" + convert.str();
  
	out << "(and ";
	trans(my_analysis, til->effs, i, out);
	out << " (=" << tilTime << " " << til->time_stamp <<  "))";
      }
      out << ")";
      

    }
    else{
      LOG(ERROR) << "Initial State uses an unsupported timed effect type";
    }
  }

  //my_timed_effects.write(LOG(INFO));
}

void translate::trans(VAL::analysis* my_analysis, VAL::goal *goal, int start_time, int end_time, std::ofstream& out){
  constraint_goal *my_constraint_goal;
  preference *my_preference;
  simple_goal *my_simple_goal;
  qfied_goal *my_qfied_goal;
  conj_goal *my_conj_goal;
  disj_goal *my_disj_goal;
  imply_goal *my_imply_goal;
  neg_goal *my_neg_goal;
  timed_goal *my_timed_goal;
  comparison *my_comparison;
  
  string time;
  if(end_time == -1){ // only care about start time
    ostringstream convert;
    convert << start_time; 
    time = "t" + convert.str();
  } else { // only care about overall (end times are rewritten as start times in recursive call for timed goals)
    time = "t";
  }

  if(my_constraint_goal = dynamic_cast<constraint_goal*>(goal)){
    LOG(ERROR) << "Constraint goals not supported";
  } else if(my_preference = dynamic_cast<preference*>(goal)){
    LOG(ERROR) << "Preference goals not supported";
  } else if(my_simple_goal = dynamic_cast<simple_goal*>(goal)){
    if (start_time == -1){
      LOG(ERROR) << "Translating simple goal with no start_time";
    }
    my_simple_goal->setWriteController((auto_ptr<WriteController>)getWriteController());
    out << "(";
    if(my_simple_goal->getPolarity() == E_NEG){
      out << "not ";
    }
    my_simple_goal->write(out);
    out << "_" << time << ")";
  } else if(my_qfied_goal = dynamic_cast<qfied_goal*>(goal)){
        LOG(ERROR) << "Quantified goals not supported";
  } else if(my_conj_goal = dynamic_cast<conj_goal*>(goal)){
    my_conj_goal->setWriteController((auto_ptr<WriteController>)getWriteController());
    out << "(and";
    for(goal_list::iterator i = my_conj_goal->getGoals()->begin();
	i!=  my_conj_goal->getGoals()->end(); i++){
      out << " ";
      trans(my_analysis, *i, start_time, end_time, out);
    }
    out << ")";
  } else if(my_disj_goal = dynamic_cast<disj_goal*>(goal)){
        LOG(ERROR) << "Disjunctive goals not supported";
  } else if(my_imply_goal = dynamic_cast<imply_goal*>(goal)){
    LOG(ERROR) << "Disjunctive goals not supported";
  } else if(my_neg_goal = dynamic_cast<neg_goal*>(goal)){
    my_neg_goal->setWriteController((auto_ptr<WriteController>)getWriteController());
    out << "(";
    out << "not ";
    trans(my_analysis,  my_neg_goal->getGoal(), start_time, end_time, out);
    out  << ")";
  } else if(my_timed_goal = dynamic_cast<timed_goal*>(goal)){
    my_timed_goal->setWriteController((auto_ptr<WriteController>)getWriteController());
    if(my_timed_goal->getTime() == VAL::E_AT_START){
      if(start_time >= 0 && end_time == -1){
	trans(my_analysis, my_timed_goal->getGoal(), start_time, -1, out);
      }
    } else if(my_timed_goal->getTime() == VAL::E_AT_END){
      if(start_time == -1 && end_time >= 0){
	trans(my_analysis, my_timed_goal->getGoal(), end_time, -1, out);
      }
    } else if(my_timed_goal->getTime() == VAL::E_OVER_ALL){
      if(start_time >= 0 && end_time >= 0){
	trans(my_analysis, my_timed_goal->getGoal(), start_time, end_time, out);
      }
    } else {
      LOG(ERROR) << "Unsupported timed goal type: " << my_timed_goal->getTime();
    }
  } else if(my_comparison = dynamic_cast<comparison*>(goal)){
    out << "(";
    trans(my_comparison->getOp(), out);
    out << " ";
    trans(my_analysis, my_comparison->getLHS(), start_time, out);
    out << " ";
    trans(my_analysis, my_comparison->getRHS(), start_time, out);
    out << ")";
  }

}
void translate::trans(const VAL::comparison_op op, std::ofstream& out){
  if (op == VAL::E_GREATER){
    out << ">";
  } else if (op == VAL::E_GREATEQ){
    out << ">=";
  } else if (op == VAL::E_LESS){
    out << "<";
  } else if (op == VAL::E_LESSEQ){
    out << "<=";
  } else if (op == VAL::E_EQUALS){
    out << "=";
  }
}


void translate::trans_duration_comparison(VAL::analysis* my_analysis, 
					  VAL::comparison *my_comparison,
					  VAL::operator_* my_operator,
					  int act_time, 
					  int dur_time, 
					  std::ofstream& out){
  out << "(";
  trans(my_comparison->getOp(), out);
  out << " ";
  //trans(my_analysis, my_comparison->getLHS(), time, out);
  out << "duration_" << my_operator->name->getName() << "_t" << act_time;
  out << " ";
  trans(my_analysis, my_comparison->getRHS(), dur_time, out);
  out << ")";
 }

void translate::trans(VAL::analysis* my_analysis, VAL::durative_action *my_durative_action, int time, std::ofstream& out){

  // translate duration constraint
  VAL::goal *my_dur_constraint = my_durative_action->dur_constraint;
  VAL::conj_goal *my_conj_goal;
  VAL::comparison *my_comparison;
  VAL::timed_goal *my_timed_goal;

  LOG(INFO) << "Translating Durative Action: " << my_durative_action->name->getName() << " at time " << time;
  //my_dur_constraint->write(LOG(INFO));

  if (my_conj_goal = dynamic_cast<conj_goal*>(my_dur_constraint)){
    out << "(and";
    for(VAL::goal_list::iterator i = my_conj_goal->getGoals()->begin();
	i!=  my_conj_goal->getGoals()->end(); i++){
      if (my_comparison = dynamic_cast<comparison*>(*i)){
	trans_duration_comparison(my_analysis, my_comparison, my_durative_action, time, time, out);
      } else if (my_timed_goal = dynamic_cast<timed_goal*>(*i)){
	 if (my_comparison = dynamic_cast<comparison*>(*i)){
	   // todo
	 } else {
	   LOG(ERROR) << "Timed Constraint on Duration is no a comparison";
	 }
      }       
    }
    out << ")";
  } else if (my_comparison = dynamic_cast<comparison*>(my_dur_constraint)){
    trans_duration_comparison(my_analysis, my_comparison, my_durative_action, time, time, out);
  } else if (my_timed_goal = dynamic_cast<timed_goal*>(my_dur_constraint)){
    if (my_comparison = dynamic_cast<comparison*>(my_timed_goal->getGoal())){
      if (my_timed_goal->getTime() == VAL::E_AT_START){
	out << "(imply (" 
	    << my_durative_action->name->getName() << "_start_t" << time << ") ";
	trans_duration_comparison(my_analysis, my_comparison, my_durative_action, time, time, out);
	out << ")";
      } else if (my_timed_goal->getTime() == VAL::E_AT_END){
	//start at time and end at i
       	for (int i = time+1; i <= FLAGS_num_happenings; i++){
	  out << "(imply (and ("
	      << my_durative_action->name->getName() << "_start_t" << time << ") ("
	      << my_durative_action->name->getName() << "_end_t" << i << ")";
	  for (int j = time+1; j < i; j++){
	    out << " (" << my_durative_action->name->getName() << "_cont_t" << j << ")";
	  }
	  out << ") ";
	  trans_duration_comparison(my_analysis, my_comparison, my_durative_action, time, i, out);
	  out << ")";
	}
      } else {
	LOG(ERROR) << "Using illegal time spec for duration constraint";
      }
     
    } else {
      LOG(ERROR) << "Timed Constraint on Duration is no a comparison";
    }
  } 
  


  //Action duration coherence
  for (int i = time+1; i <= FLAGS_num_happenings; i++){
    out << "(imply (and ("
	<< my_durative_action->name->getName() << "_start_t" << time << ") ("
	<< my_durative_action->name->getName() << "_end_t" << i << ")";
    for (int j = time+1; j < i; j++){
      out << " (" << my_durative_action->name->getName() << "_cont_t" << j << ")";
    }
    out << ") (= (- t" << i << " t" << time << ") (duration_" << my_durative_action->name->getName() << "_t" << time << ")))";
  }

  //at-start precondition
  out << "(imply ("
      << my_durative_action->name->getName() << "_start_t" << time << ") ";
  VAL::goal* my_precondition = my_durative_action->precondition;
  trans(my_analysis, my_precondition, time, -1, out); // -1 indicates that we ignore at end and overall
  out << ")";
  
  //at-end and overall preconditions
  for (int i = time+1; i <= FLAGS_num_happenings; i++){
    // at-end
    out << "(imply ("
	<< my_durative_action->name->getName() << "_end_t" << time << ") ";
    trans(my_analysis, my_precondition, -1, i, out); // -1 indicates that we ignore at start and overall
    out << ")";

    // overall
    out << "(imply (and ("
	<< my_durative_action->name->getName() << "_end_t" << time << ") ("
	<< my_durative_action->name->getName() << "_start_t" << time << ")) "
	<< "(forall t [t" << time << " t" << i <<"] ";
    trans(my_analysis, my_precondition, time, i, out); 
    out << ")";
    out << ")";
  }


}

void translate::trans(VAL::analysis* my_analysis, VAL::expression *my_expression, int time, std::ofstream& out){
  VAL::plus_expression *my_plus_expression;
  VAL::minus_expression *my_minus_expression;
  VAL::mul_expression *my_mul_expression;
  VAL::div_expression *my_div_expression;
  VAL::uminus_expression *my_uminus_expression;
  VAL::int_expression *my_int_expression;
  VAL::float_expression *my_float_expression;
  VAL::func_term *my_func_term;
  VAL::class_func_term *my_class_func_term;
  VAL::special_val_expr *my_special_val_expr;

  if (my_plus_expression = dynamic_cast<VAL::plus_expression*>(my_expression)){
    out << "(+ ";
    trans(my_analysis, my_plus_expression->getLHS(), time, out);
    out << " ";
    trans(my_analysis, my_plus_expression->getRHS(), time, out);
    out << ")";
  } else if (my_minus_expression = dynamic_cast<VAL::minus_expression*>(my_expression)){
    out << "(- ";
    trans(my_analysis, my_minus_expression->getLHS(), time, out);
    out << " ";
    trans(my_analysis, my_minus_expression->getRHS(), time, out);
    out << ")";
  } else if (my_mul_expression = dynamic_cast<VAL::mul_expression*>(my_expression)){
    out << "(* ";
    trans(my_analysis, my_mul_expression->getLHS(), time, out);
    out << " ";
    trans(my_analysis, my_mul_expression->getRHS(), time, out);
    out << ")";
  } else if (my_div_expression = dynamic_cast<VAL::div_expression*>(my_expression)){
    out << "(/ ";
    trans(my_analysis, my_div_expression->getLHS(), time, out);
    out << " ";
    trans(my_analysis, my_div_expression->getRHS(), time, out);
    out << ")";
  } else if (my_uminus_expression = dynamic_cast<VAL::uminus_expression*>(my_expression)){
    out << "(- ";
    trans(my_analysis, my_uminus_expression->getExpr(), time, out);
    out << ")";
  } else if (my_int_expression = dynamic_cast<VAL::int_expression*>(my_expression)){
    out << my_int_expression->double_value();
  } else if (my_float_expression = dynamic_cast<VAL::float_expression*>(my_expression)){
    out << my_float_expression->double_value();
  } else if (my_func_term = dynamic_cast<VAL::func_term*>(my_expression)){
    // todo
  } else if (my_class_func_term = dynamic_cast<VAL::class_func_term*>(my_expression)){
    // todo
  } else if (my_special_val_expr = dynamic_cast<VAL::special_val_expr*>(my_expression)){
    // todo
  } 

}

std::string translate::getTimepoint(double t){
  timemap::iterator tps = timepoints.find(t);
  std::string time;
  if(tps == timepoints.end()){
    ostringstream convert;
    convert << timepoints.size();
    time = "t" + convert.str();
    timepoints[t] = time;
  } else {
    time = (*tps).second;
  }  
  return time;
}
