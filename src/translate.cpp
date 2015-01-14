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
#include <sstream>

using namespace VAL;

DEFINE_string(outfile, "out.smt2", "SMT2 output file");
DEFINE_int32(num_happenings, 0, "Number of happenings");

void translate::translateSMT(VAL::analysis* my_analysis){
  LOG(INFO) << "Translating Analysis";

  std::ofstream out((string)FLAGS_outfile);
  std::stringstream function_declaration;
  std::stringstream ode_declaration;
  std::stringstream bounds_declaration;
  std::stringstream constraint_declaration;

  if(!out) LOG(ERROR) << "Could not open output file: " << FLAGS_outfile;

  problem* my_problem = my_analysis->the_problem;
  domain* my_domain   = my_analysis->the_domain;

  out << "(set-logic QF_NRA_ODE)\n";





  // Initial State
  effect_lists* my_initial_state = my_problem->initial_state;
  constraint_declaration << "\n//------------ START Initial State ------------//\n"; 
    trans(my_analysis, my_initial_state, NULL, 0, constraint_declaration);
    constraint_declaration << "\n//------------ END Initial State ------------//\n";

    // Goal
    constraint_declaration << "\n//------------ START Goal ------------//\n"; 
    goal *my_goal = my_problem->the_goal;
    constraint_declaration << "(or ";
    for(int i = 0; i <= FLAGS_num_happenings; i++){
      trans(my_analysis, my_goal, NULL, i, -1, constraint_declaration);
      function_declaration << "(declare-fun time_" << i <<" () Real)\n";	      
      bounds_declaration << "(assert (<= 0 time_" << i << "))\n";
      bounds_declaration << "(assert (<= time_" << i << " 1000))\n"; //magic number

    }
    constraint_declaration << ")";
    constraint_declaration << "\n//------------ END Goal ------------//\n";

    operator_list* ops = my_domain->ops; 
 
    list<VAL::const_symbol*> constants;
    if (my_problem->objects != NULL){
      for (const_symbol_list::iterator i = my_problem->objects->begin(); i != my_problem->objects->end(); i++){
	//    LOG(INFO) << "Got object: " << (*i)->getName() << " - " << (*i)->type->getName();
	constants.push_back(*i);
      }
    }
    if (my_domain->constants != NULL){
      for(const_symbol_list::iterator i = my_domain->constants->begin(); i != my_domain->constants->end(); i++){
	// LOG(INFO) << "Got constant: " << (*i)->getName() << " - " << (*i)->type->getName();
	constants.push_back(*i);
      }
    }


    for(operator_list::iterator op = ops->begin(); op != ops->end(); op++){

      std::list<param_grounding*>* groundings = get_groundings((*op)->parameters, &constants);

      action *my_action;
      event *my_event;
      process *my_process;
      durative_action *my_durative_action;
    
      for(std::list<param_grounding*>::iterator grounding = groundings->begin(); grounding != groundings->end(); grounding++){
	string name = (*op)->name->getName();
	for (param_grounding::iterator var = (*grounding)->begin(); var != (*grounding)->end(); var++){
	  name += "_" + (*var).second->getName();
	}
      
	constraint_declaration << "\n//------------ START " << name << " ------------//"; 
	


	if( my_action = dynamic_cast<action*>(*op) ){
	} else if ( my_event = dynamic_cast<event*>(*op) ){
	} else if ( my_process = dynamic_cast<process*>(*op) ){
	} else if ( my_durative_action = dynamic_cast<durative_action*>(*op) ){
  

	  for(int i = 0; i <= FLAGS_num_happenings; i++){

	    function_declaration << "(declare-fun duration_" << name << "_time_" << i << " () Real)\n";
	    bounds_declaration << "(assert (<= 0 duration_" << name << "_time_" << i << "))\n";
	    bounds_declaration << "(assert (<= duration_" << name << "_time_" << i << " 1000))\n"; //magic number


	    //function_declaration << "(declare-fun " << name << "_time_" << i << " () Bool)\n";

	    constraint_declaration << "\n// Happening " << i << "\n"; 
	    //LOG(INFO) << "Encoding " << name << " at " << i;

	      
	      if(i < FLAGS_num_happenings){
		trans(my_analysis, my_durative_action, *grounding, i, constraint_declaration);
	      }
	
	    constraint_declaration << "\n// Continuity Constraints " << i << "\n"; 
	    // action continuity
	    if(i < FLAGS_num_happenings){
	      constraint_declaration << "(=> (" << name << "_start_time_" << i <<")" 
				     << " (or ";
	      if((i+1) < FLAGS_num_happenings){
		constraint_declaration << "(" << name << "_cont_time_" << (i+1) <<") ";
	      }
	      constraint_declaration << "(" << name << "_end_time_" << (i+1) <<")))";

	      if(i > 0){
		constraint_declaration << "(=> (" << name << "_cont_time_" << i <<")" 
				       << " (or ";
		if((i+1) < FLAGS_num_happenings){
		  constraint_declaration << "(" << name << "_cont_time_" << (i+1) <<") ";
		}
		constraint_declaration << "(" << name << "_end_time_" << (i+1) <<")))";
	      }
	      
	      function_declaration << "(declare-fun " << name << "_start_time_" << i <<" () Bool)\n";

	    } 
	    if(i > 0 && i < FLAGS_num_happenings){
	      function_declaration << "(declare-fun " << name << "_cont_time_" << i <<" () Bool)\n";
	    }

	    if (i > 0){

	      constraint_declaration << "(=> (" << name << "_end_time_" << i <<")" 
				     << " (or ";
	      if((i-1) > 0){
		constraint_declaration << "(" << name << "_cont_time_" << (i-1) <<") ";
	      }
	      constraint_declaration << "(" << name << "_start_time_" << (i-1) <<")))";

	      if(i < FLAGS_num_happenings){
		constraint_declaration << "(=> (" << name << "_cont_time_" << i <<")" 
				       << " (or ";
		if((i-1) > 0){
		  constraint_declaration << "(" << name << "_cont_time_" << (i-1) <<") ";
		}
		constraint_declaration << "(" << name << "_start_time_" << (i-1) <<")))";
	      }



	  
	      function_declaration << "(declare-fun " << name << "_end_time_" << i <<" () Bool)\n";	      

	    }
	  } 

	  constraint_declaration << "\n// Continuity Constraints Extreme Points\n";
	  //Actions don't continue at extreme time points
	    // constraint_declaration << "(not (" << name << "_cont_time_0))";
	    // constraint_declaration << "(not (" << name << "_cont_time_" << FLAGS_num_happenings << "))";
	}
	constraint_declaration << "\n//------------ END " << name << " ------------//\n"; 

      }

      for(std::list<param_grounding*>::iterator i = groundings->begin(); i != groundings->end(); i++){
	delete *i;
      }
      delete groundings;
    }


    //get proposition declarations
    for(int time = 0; time <= FLAGS_num_happenings; time++){
      for(pred_decl_list::iterator funcs = my_domain->predicates->begin(); funcs != my_domain->predicates->end(); funcs++){
	std::list<param_grounding*>* groundings = get_groundings((*funcs)->getArgs(), &constants);
	for(std::list<param_grounding*>::iterator grounding = groundings->begin(); grounding != groundings->end(); grounding++){
	  string name = (*funcs)->getPred()->getName();
	  for (param_grounding::iterator var = (*grounding)->begin(); var != (*grounding)->end(); var++){
	    name += "_" + (*var).second->getName();
	  }
	  function_declaration << "(declare-fun " << name << "_time_" << time << " () Bool)\n";
	}
      }
    }

    for(int time = 0; time < FLAGS_num_happenings; time++){
      constraint_declaration << "\n//------------ START Concurrent Increases ------------//\n";
      for(func_decl_list::iterator funcs = my_domain->functions->begin(); funcs != my_domain->functions->end(); funcs++){
	std::list<param_grounding*>* groundings = get_groundings((*funcs)->getArgs(), &constants);
	for(std::list<param_grounding*>::iterator grounding = groundings->begin(); grounding != groundings->end(); grounding++){
	  string name = (*funcs)->getFunction()->getName();
	  for (param_grounding::iterator var = (*grounding)->begin(); var != (*grounding)->end(); var++){
	    name += "_" + (*var).second->getName();
	  }
	  
	  function_declaration << "(declare-fun " << name << "_time_" << time << " () Real)\n";
	  bounds_declaration << "(assert (<= -10000 " << name << "_time_" << time << "))\n"; //magic number
	  bounds_declaration << "(assert (<= " << name << "_time_" << time << " 10000))\n"; //magic number
	  if(time+1 == FLAGS_num_happenings){
	    function_declaration << "(declare-fun " << name << "_time_" << (time+1) << " () Real)\n";
	    function_declaration << "(declare-fun " << name << " () Real)\n";
	  bounds_declaration << "(assert (<= -10000 " << name << "_time_" << (time+1) << "))\n"; //magic number
	  bounds_declaration << "(assert (<= " << name << "_time_" << (time+1) << " 10000))\n"; //magic number
	  bounds_declaration << "(assert (<= -10000 " << name << "))\n"; //magic number
	  bounds_declaration << "(assert (<= " << name << " 10000))\n"; //magic number
	  }

	  constraint_declaration << "\n// Concurrent for fuction: " << name << "\n";

	  // negate assigners
	  set<string>* assigners = fassigners[name];
	  if(assigners != NULL && !assigners->empty()){
	    constraint_declaration << "(not (or ";
	    for(set<string>::iterator fa = assigners->begin(); fa != assigners->end(); fa++){
	      constraint_declaration << "(" << *fa << "_time_" << time << ")";
	    }
	    constraint_declaration << "))";
	  }

	}
      }

      // for(fincrementmap::iterator fi = fincrementers.begin(); fi != fincrementers.end(); fi++){
      //   for(fassignmentmap::iterator fa = fassigners.begin(); fa != fassigners.end(); fa++){
      //   }
      //   }
      constraint_declaration << "\n//------------ END Concurrent Increases ------------//\n";
      constraint_declaration << "\n//------------ START Concurrent Continuous ------------//\n";
      for(int time = 0; time < FLAGS_num_happenings; time++){
	std::stringstream current_vars;
	std::stringstream next_vars;
      

	constraint_declaration << "\n// Time " << time << "\n";
	ode_declaration << "(define-ode flow_" << time << " (";
	set<string> gammas;
	  for(func_decl_list::iterator funcs = my_domain->functions->begin(); funcs != my_domain->functions->end(); funcs++){
	    std::list<param_grounding*>* groundings = get_groundings((*funcs)->getArgs(), &constants);
	    for(std::list<param_grounding*>::iterator grounding = groundings->begin(); grounding != groundings->end(); grounding++){
	      string name = (*funcs)->getFunction()->getName();
	      for (param_grounding::iterator var = (*grounding)->begin(); var != (*grounding)->end(); var++){
		name += "_" + (*var).second->getName();
	      }
	      //out << "\n// Concurrent Continuous for fuction: " << name << "\n";

		// sum influences
	      set<string>* influences = fcontinuousers[name];
	      // for(fcontinuousmap::iterator f = fcontinuousers.begin(); f != fcontinuousers.end(); f++){
	      //   out << (*f).first << ": ";
	      //   if((*f).second != NULL){
	      //   for(set<string>::iterator s = (*f).second->begin(); s != (*f).second->end(); s++){
	      //     out << *s << ",";
	      //   }
	      //   }
	      //   out << "\n";
	      // }

	      //(define-ode flow_time ((= d/dt[f1] (+ inf1 inf2 ...)) (= d/dt[f2] (+ inf1 inf2 ...))))
	      //(= [f1_time+1 f2_time+1] (integral 0. time+1 flow_time))
	      ode_declaration << "(= d/dt[" << name << "] ";
	      next_vars << name << "_time_" << (time+1) << " ";
	      current_vars << name << "_time_" << time << " ";

	      if(influences != NULL && !influences->empty()){
		ode_declaration << "(+ ";
		for(set<string>::iterator fa = influences->begin(); fa != influences->end(); fa++){
		  ode_declaration << "gamma_" << *fa << "_" << name 
		    //<< "_time_" << time << "_time_" << (time+1) 
				  << " ";
		  function_declaration << "(declare-fun gamma_" << *fa << "_" << name << "_time_" << time <<   " () Real)\n";
		  gammas.insert("gamma_" + *fa + "_" + name);
		  if(time == FLAGS_num_happenings-1){
		    function_declaration << "(declare-fun gamma_" << *fa << "_" << name << "_time_" << (time+1) <<   " () Real)\n";
		  }
		  function_declaration << "(declare-fun gamma_" << *fa << "_" << name << " () Real)\n";
		}
		ode_declaration << ")";
	      }
	      else {
		ode_declaration << "0";
	      }
	    }
	    ode_declaration << ")";
	
	  }
	  for(std::set<string>::iterator g = gammas.begin(); g != gammas.end(); g++){
	    ode_declaration << "(= d/dt[" << *g << "] 0)";
	    next_vars << *g << "_time_" << (time+1) << " ";
	    current_vars << *g << "_time_" << time << " ";
	  }


	  ode_declaration << "))\n";
	  constraint_declaration << "(= [" << next_vars.str() << "] (integral time_" << time << " time_" << (time+1) 
				 << " ["  << current_vars.str() << "]" << " flow_" << time << "))";

      }
      constraint_declaration << "\n//------------ END Concurrent Continuous ------------//\n";
    }

    constraint_declaration << "\n//------------ START Frame Axioms ------------//\n";
    // todo frame for discrete vars
    // for(int time = 0; time < FLAGS_num_happenings; time++){
    //   constraint_declaration << "\n// Frame at time " << time << "\n";
    //   for(func_decl_list::iterator funcs = my_domain->functions->begin(); funcs != my_domain->functions->end(); funcs++){
    // 	std::list<param_grounding*>* groundings = get_groundings((*funcs)->getArgs(), &constants);
    // 	for(std::list<param_grounding*>::iterator grounding = groundings->begin(); grounding != groundings->end(); grounding++){
    // 	  string name = (*funcs)->getFunction()->getName();
    // 	  for (param_grounding::iterator var = (*grounding)->begin(); var != (*grounding)->end(); var++){
    // 	    name += "_" + (*var).second->getName();
    // 	  }
    // 	  //for action/event/process effecting literal
    // 	  //  negate happening at time
    // 	  //implies
    // 	  // funtion persists

    // 	  constraint_declaration << "(=> ";

    // 	  set<string>* influences = fcontinuousers[name];

    // 	  if(influences != NULL && !influences->empty()){
    // 	    constraint_declaration << "(not (or ";
    // 	    for(set<string>::iterator fa = influences->begin(); fa != influences->end(); fa++){
    // 	      constraint_declaration <<  *fa << "_t" << time << " ";
    // 	    }
    // 	    constraint_declaration << "))";
    // 	  }
    // 	  else {
    // 	    constraint_declaration << "true ";
    // 	  }
    // 	  constraint_declaration << "(= " << name << "_t" << (time+1) << " " << name << "_t" << time << "))";
   
    // 	}
    //   }
    // }
    constraint_declaration << "\n//------------ END Frame Axioms ------------//\n";


    constraint_declaration << "\n//------------ START Timepoint order ------------//\n";
    for(int time = 0; time < FLAGS_num_happenings; time++){
      constraint_declaration << "(<= time_" << time << " time_" << (time+1) << ")";
    }
    constraint_declaration << "\n//------------ END Timepoint order ------------//\n";
    
    
    
    out << function_declaration.str();
    out << ode_declaration.str();
    out << bounds_declaration.str();
    out << "(assert (and";
    out << constraint_declaration.str();    
    out << "))\n"; 
    out << "(check-sat)\n"
	<< "(exit)\n";
LOG(INFO) << "Finished Translating.";
    out.close();

}


std::list<param_grounding*>* translate::get_groundings(VAL::var_symbol_list *symbols, list<VAL::const_symbol*> *constants){
  std::list<param_grounding*> *groundings = new std::list<param_grounding*>();
  param_grounding current_grounding;
  get_groundings_rec(symbols,  constants, groundings, &current_grounding, symbols->begin());   
  return groundings;
}


std::list<param_grounding*>* 
translate::get_groundings_rec(VAL::var_symbol_list *symbols,
			      list<VAL::const_symbol*> *constants, 
			      std::list<param_grounding*> *groundings, 
			      param_grounding* current_grounding,
			      var_symbol_list::iterator parameters
			      ){ 
  
  if (parameters == symbols->end()){
    //LOG(INFO) << "Got ground operator: ";
    // for (var_symbol_list::iterator i = op->parameters->begin(); i != op->parameters->end(); i++){
    //   LOG(INFO) << (*i)->getName() << " = " << (*current_grounding)[*i]->getName();      
    // }
    param_grounding* copy = new param_grounding();
    for(param_grounding::iterator i = current_grounding->begin(); i != current_grounding->end(); i++){
      (*copy)[(*i).first] = (*i).second;
    }
    groundings->push_back( copy );

  } else {
    var_symbol *current_param = *parameters;
    parameters++;

    //LOG(INFO) << "Param: " << current_param->getName();

    for (list<VAL::const_symbol*>::iterator i = constants->begin(); 
	 i != constants->end(); i++){
      if ( current_param->type == (*i)->type ) {
	(*current_grounding)[current_param] = *i;
	get_groundings_rec(symbols, constants, groundings, current_grounding, parameters);
      }
    }
    parameters--;
  }
  
}

/* meant for initial state */
void translate::trans(VAL::analysis* my_analysis, VAL::effect_lists *ef_lists, param_grounding* grounding, int tm, std::iostream& out){
  
  ostringstream convert;
  convert << tm; 
  string time = "time_" + convert.str();


  pc_list<simple_effect*> my_add_effects = ef_lists->add_effects;
  for(pc_list<simple_effect*>::iterator i = my_add_effects.begin();
      i != my_add_effects.end(); i++){
    (*i)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    out << "(";
    (*i)->prop->write(out);
    out << "_" << time << ")";
  }

  pc_list<simple_effect*> my_del_effects = ef_lists->del_effects;
  for(pc_list<simple_effect*>::iterator i = my_del_effects.begin();
      i != my_del_effects.end(); i++){
    (*i)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    out << "(not (";
    (*i)->prop->write(out);
    out << "_" << time << "))";
  }

  pc_list<assignment*> my_assign_effects = ef_lists->assign_effects;
  for(pc_list<assignment*>::iterator i = my_assign_effects.begin();
      i != my_assign_effects.end(); i++){
    (*i)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
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
      til->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
      out << "(or ";
      for(int i = 0; i <= FLAGS_num_happenings; i++){     
	ostringstream convert;
	convert << i; 
	string tilTime = "t" + convert.str();
  
	out << "(and ";
	trans(my_analysis, til->effs, grounding, i, out);
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

void translate::trans(VAL::analysis* my_analysis, VAL::goal *goal, param_grounding* grounding, int start_time, int end_time, std::iostream& out){
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
    time = "time_" + convert.str();
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
    my_simple_goal->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    out << "(";
    if(my_simple_goal->getPolarity() == E_NEG){
      out << "not ";
    }
    my_simple_goal->write(out);
    out << "_" << time << ")";
  } else if(my_qfied_goal = dynamic_cast<qfied_goal*>(goal)){
    LOG(ERROR) << "Quantified goals not supported";
  } else if(my_conj_goal = dynamic_cast<conj_goal*>(goal)){
    my_conj_goal->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    out << "(and";
    for(goal_list::iterator i = my_conj_goal->getGoals()->begin();
	i!=  my_conj_goal->getGoals()->end(); i++){
      out << " ";
      trans(my_analysis, *i, grounding, start_time, end_time, out);
    }
    out << ")";
  } else if(my_disj_goal = dynamic_cast<disj_goal*>(goal)){
    LOG(ERROR) << "Disjunctive goals not supported";
  } else if(my_imply_goal = dynamic_cast<imply_goal*>(goal)){
    LOG(ERROR) << "Disjunctive goals not supported";
  } else if(my_neg_goal = dynamic_cast<neg_goal*>(goal)){
    my_neg_goal->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    out << "(";
    out << "not ";
    trans(my_analysis,  my_neg_goal->getGoal(), grounding, start_time, end_time, out);
    out  << ")";
  } else if(my_timed_goal = dynamic_cast<timed_goal*>(goal)){
    my_timed_goal->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    if(my_timed_goal->getTime() == VAL::E_AT_START){
      if(start_time >= 0 && end_time == -1){
	trans(my_analysis, my_timed_goal->getGoal(), grounding, start_time, -1, out);
      }
    } else if(my_timed_goal->getTime() == VAL::E_AT_END){
      if(start_time == -1 && end_time >= 0){
	trans(my_analysis, my_timed_goal->getGoal(), grounding, end_time, -1, out);
      }
    } else if(my_timed_goal->getTime() == VAL::E_OVER_ALL){
      if(start_time >= 0 && end_time >= 0){
	trans(my_analysis, my_timed_goal->getGoal(), grounding, start_time, end_time, out);
      }
    } else {
      LOG(ERROR) << "Unsupported timed goal type: " << my_timed_goal->getTime();
    }
  } else if(my_comparison = dynamic_cast<comparison*>(goal)){
    out << "(";
    trans(my_comparison->getOp(), out);
    out << " ";
    trans(my_analysis, my_comparison->getLHS(), grounding, start_time, out);
    out << " ";
    trans(my_analysis, my_comparison->getRHS(), grounding, start_time, out);
    out << ")";
  }

}
void translate::trans(const VAL::comparison_op op, std::iostream& out){
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
					  param_grounding* grounding, 
					  int act_time, 
					  int dur_time, 
					  std::iostream& out){
  out << "(";
  trans(my_comparison->getOp(), out);
  out << " ";
  //trans(my_analysis, my_comparison->getLHS(), time, out);

  string name = my_operator->name->getName();
  for (param_grounding::iterator var = grounding->begin(); var != grounding->end(); var++){
    name += "_" + (*var).second->getName();
  }



  out << "duration_" << name << "_time_" << act_time;
  out << " ";
  trans(my_analysis, my_comparison->getRHS(), grounding, dur_time, out);
  out << ")";
}

void translate::get_precond_types(bool* types, VAL::goal* goal){
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
  
  if(my_qfied_goal = dynamic_cast<qfied_goal*>(goal)){
    LOG(ERROR) << "Quantified goals not supported";
  } else if(my_conj_goal = dynamic_cast<conj_goal*>(goal)){
    for(goal_list::iterator i = my_conj_goal->getGoals()->begin();
	i!=  my_conj_goal->getGoals()->end(); i++){
      get_precond_types(types, *i);
    }
  } else if(my_disj_goal = dynamic_cast<disj_goal*>(goal)){
    LOG(ERROR) << "Disjunctive goals not supported";
  } else if(my_imply_goal = dynamic_cast<imply_goal*>(goal)){
    LOG(ERROR) << "Disjunctive goals not supported";
  } else if(my_neg_goal = dynamic_cast<neg_goal*>(goal)){
    get_precond_types(types, my_neg_goal->getGoal());
  } else if(my_timed_goal = dynamic_cast<timed_goal*>(goal)){
    if(my_timed_goal->getTime() == VAL::E_AT_START){
      types[0] = true;
    } else if(my_timed_goal->getTime() == VAL::E_AT_END){
      types[1] = true;
    } else if(my_timed_goal->getTime() == VAL::E_OVER_ALL){
      types[2] = true;
    } else {
      LOG(ERROR) << "Unsupported timed goal type: " << my_timed_goal->getTime();
    }
  }
}

void translate::get_effect_types(bool* effect_types,  VAL::effect_lists *ef_lists){
  

  // pc_list<simple_effect*> my_add_effects = ef_lists->add_effects;
  // for(pc_list<simple_effect*>::iterator i = my_add_effects.begin();
  //     i != my_add_effects.end(); i++){
  //   (*i)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
  //   out << "(";
  //   (*i)->prop->write(out);
  //   out << "_" << time << ")";
  // }

  // pc_list<simple_effect*> my_del_effects = ef_lists->del_effects;
  // for(pc_list<simple_effect*>::iterator i = my_del_effects.begin();
  //     i != my_del_effects.end(); i++){
  //   (*i)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
  //   out << "(not (";
  //   (*i)->prop->write(out);
  //   out << "_" << time << "))";
  // }

  // pc_list<assignment*> my_assign_effects = ef_lists->assign_effects;
  // for(pc_list<assignment*>::iterator i = my_assign_effects.begin();
  //     i != my_assign_effects.end(); i++){
  //   (*i)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
  //   if((*i)->getOp() == VAL::E_ASSIGN){
  //     out << "(= ";
  //     (*i)->getFTerm()->write(out);
  //     out << "_" << time << " ";
  //     (*i)->getExpr()->write(out);
  //     out << ")";
  //   } else {
  //     LOG(ERROR) << "Unhandled Assignment type in effect" << (*i)->getOp();
  //   }
  // }


  pc_list<timed_effect*> my_timed_effects = ef_lists->timed_effects;
  for(pc_list<timed_effect*>::iterator i = my_timed_effects.begin();
      i != my_timed_effects.end(); i++){
    VAL::effect_lists* tef_list = (*i)->effs;
    pc_list<assignment*> my_assign_effects = tef_list->assign_effects;
    pc_list<simple_effect*> my_add_effects = tef_list->add_effects;
    pc_list<simple_effect*> my_del_effects = tef_list->del_effects;

    if((*i)->ts == VAL::E_AT_START){
      if(!my_add_effects.empty()){
	effect_types[0] = true;
      }
      if(!my_del_effects.empty()){
	effect_types[0] = true;
      }

      for(pc_list<assignment*>::iterator j = my_assign_effects.begin();
	  j != my_assign_effects.end(); j++){
	if((*j)->getOp() == VAL::E_ASSIGN){
	  effect_types[0] = true;
	} else if((*j)->getOp() == VAL::E_INCREASE || (*j)->getOp() == VAL::E_DECREASE ){
	  effect_types[2] = true;
	}
      }
    } else if ((*i)->ts == VAL::E_AT_END){
      if(!my_add_effects.empty()){
	effect_types[1] = true;
      }
      if(!my_del_effects.empty()){
	effect_types[1] = true;
      }


      for(pc_list<assignment*>::iterator j = my_assign_effects.begin();
	  j != my_assign_effects.end(); j++){
	if((*j)->getOp() == VAL::E_ASSIGN){
	  effect_types[1] = true;
	} else if((*j)->getOp() == VAL::E_INCREASE || (*j
						       )->getOp() == VAL::E_DECREASE ){
	  effect_types[3] = true;
	}
      }

    } else if ((*i)->ts == VAL::E_CONTINUOUS){
      effect_types[4] = true;
    }
    
  }

  //my_timed_effects.write(LOG(INFO));
}

void translate::trans(VAL::analysis* my_analysis, VAL::durative_action *my_durative_action, param_grounding* grounding, int time, std::iostream& out){

  // translate duration constraint
  VAL::goal *my_dur_constraint = my_durative_action->dur_constraint;
  VAL::conj_goal *my_conj_goal;
  VAL::comparison *my_comparison;
  VAL::timed_goal *my_timed_goal;

  string name = my_durative_action->name->getName();
  for (param_grounding::iterator var = grounding->begin(); var != grounding->end(); var++){
    name += "_" + (*var).second->getName();
  }

  LOG(INFO) << "Translating Durative Action: " << name << " at time " << time;
  //my_dur_constraint->write(LOG(INFO));

  out << "\n// Duration Constraint\n";
  if (my_conj_goal = dynamic_cast<conj_goal*>(my_dur_constraint)){
    out << "(and";
    for(VAL::goal_list::iterator i = my_conj_goal->getGoals()->begin();
	i!=  my_conj_goal->getGoals()->end(); i++){
      if (my_comparison = dynamic_cast<comparison*>(*i)){
	trans_duration_comparison(my_analysis, my_comparison, my_durative_action, grounding, time, time, out);
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
    trans_duration_comparison(my_analysis, my_comparison, my_durative_action, grounding, time, time, out);
  } else if (my_timed_goal = dynamic_cast<timed_goal*>(my_dur_constraint)){
    if (my_comparison = dynamic_cast<comparison*>(my_timed_goal->getGoal())){
      if (my_timed_goal->getTime() == VAL::E_AT_START){
	out << "(=> (" 
	    << name << "_start_time_" << time << ") ";
	trans_duration_comparison(my_analysis, my_comparison, my_durative_action, grounding, time, time, out);
	out << ")";
      } else if (my_timed_goal->getTime() == VAL::E_AT_END){
	//start at time and end at i
       	for (int i = time+1; i <= FLAGS_num_happenings; i++){
	  out << "(=> (and ("
	      << name << "_start_time_" << time << ") ("
	      << name << "_end_time_" << i << ")";
	  for (int j = time+1; j < i; j++){
	    out << " (" << name << "_cont_time_" << j << ")";
	  }
	  out << ") ";
	  trans_duration_comparison(my_analysis, my_comparison, my_durative_action, grounding, time, i, out);
	  out << ")";
	}
      } else {
	LOG(ERROR) << "Using illegal time spec for duration constraint";
      }
     
    } else {
      LOG(ERROR) << "Timed Constraint on Duration is no a comparison";
    }
  } 
  

  out << "\n// Duration Coherence\n";
  //Action duration coherence
  for (int i = time+1; i <= FLAGS_num_happenings; i++){
    out << "(=> (and ("
	<< name << "_start_time_" << time << ") ("
	<< name << "_end_time_" << i << ")";
    for (int j = time+1; j < i; j++){
      out << " (" << name << "_cont_time_" << j << ")";
    }
    out << ") (= (- time_" << i << " time_" << time << ") (duration_" << name << "_time_" << time << ")))";
  }


  VAL::goal* my_precondition = my_durative_action->precondition;

  const int at_start_index = 0;
  const int at_end_index = 1;
  const int overall_index = 2;
  bool precond_types[3] = { false, false, false };
  get_precond_types((bool*)&precond_types, my_precondition);

  if(precond_types[at_start_index]){
    out << "\n// At-Start Condition\n";

    //at-start precondition
    out << "(=> ("
	<< name << "_start_time_" << time << ") ";
    
    trans(my_analysis, my_precondition, grounding, time, -1, out); // -1 indicates that we ignore at end and overall
    out << ")";
  }
  

  //at-end and overall preconditions
  for (int i = time+1; i <= FLAGS_num_happenings; i++){
    if(precond_types[at_end_index]){
      out << "\n// At-End Condition\n";
      // at-end
      out << "(=> ("
	  << name << "_end_time_" << i << ") ";
      trans(my_analysis, my_precondition, grounding, -1, i, out); // -1 indicates that we ignore at start and overall
      out << ")";
    }

    if(precond_types[overall_index]){
      out << "\n// Overall Condition\n";
      // overall
      out << "(=> (and ("
	  << name << "_end_time_" << i << ") ("
	  << name << "_start_time_" << time << ")) "
	  << "(forall_t " << time << " [time_" << time << " time_" << i <<"] ";
      trans(my_analysis, my_precondition, grounding, time, i, out); 
      out << ")";
      out << ")";
    }
  }

  VAL::effect_lists* ef_lists = my_durative_action->effects;
  // const int at_start_assign_index = 0;
  // const int at_end_assign_index = 1;
  // const int at_start_increase_index = 2;
  // const int at_end_increase_index = 3;
  // const int continuous_index = 4;
  // bool effect_types[5] = { false, false, false, false, false };
  // get_effect_types((bool*)&effect_types, my_effect);


  pc_list<timed_effect*> my_timed_effects = ef_lists->timed_effects;
  for(pc_list<timed_effect*>::iterator i = my_timed_effects.begin();
      i != my_timed_effects.end(); i++){
    VAL::effect_lists* tef_list = (*i)->effs;
    pc_list<assignment*> my_assign_effects = tef_list->assign_effects;
    pc_list<simple_effect*> my_add_effects = tef_list->add_effects;
    pc_list<simple_effect*> my_del_effects = tef_list->del_effects;

    if((*i)->ts == VAL::E_AT_START){
      
      for(pc_list<simple_effect*>::iterator j = my_add_effects.begin();
	  j != my_add_effects.end(); j++){
	(*j)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
	out << "\n// At-Start Assignment Effects\n";
	out << "(=> ("
	    << name << "_start_time_" << time << ") ";
	out << "(";
	(*j)->prop->write(out);
	out << "_time_" << time << ")";
	out << ")";	  	  
      }
      for(pc_list<simple_effect*>::iterator j = my_del_effects.begin();
	  j != my_del_effects.end(); j++){
	(*j)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
	out << "\n// At-Start Assignment Effects\n";
	out << "(=> ("
	    << name << "_start_time_" << time << ") ";
	out << "(not (";
	(*j)->prop->write(out);
	out << "_time_" << time << ")";
	out << "))";	  	  
      }

      for(pc_list<assignment*>::iterator j = my_assign_effects.begin();
	  j != my_assign_effects.end(); j++){
	if((*j)->getOp() == VAL::E_ASSIGN){
	  (*j)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
	  out << "\n// At-Start Assignment Effects\n";
	  out << "(=> ("
	      << name << "_start_time_" << time << ") ";
	  out << "(= (";
	  //(*j)->getFTerm()->write(out);
	  std::stringstream str;
	  (*j)->getFTerm()->write(str);
	  out << str;

	  out << "_time_" << time << ")";
	  out << ")";
	  trans(my_analysis, (*j)->getExpr(), grounding, time, out);
	  out << ")";
	} else if((*j)->getOp() == VAL::E_INCREASE || (*j)->getOp() == VAL::E_DECREASE ){
	  out << "\n// At-Start Increase Effects\n";
	  out << "(=> ("
	      << name << "_start_time_" << time << ") ";
	  out << "(" << ((*j)->getOp() == VAL::E_INCREASE ? "+" : "-") << "= (delta_" << name << "_";
	  (*j)->getFTerm()->write(out);
	  out << "_time_" << (time+1) << ")";
	  
	  trans(my_analysis, (*j)->getExpr(), grounding, time, out);
	  out << ")";
	  out << ")";
	}
      }
    } else if ((*i)->ts == VAL::E_AT_END){
      out << "\n// At-End Assignment Effects\n";
      for (int k = time+1; k <= FLAGS_num_happenings; k++){
	if(k == 1){
	  continue;
	}

	for(pc_list<simple_effect*>::iterator j = my_add_effects.begin();
	    j != my_add_effects.end(); j++){
	  (*j)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
	  
	  out << "(=> ("
	      << name << "_end_time_" << (k-1) << ") ";
	  out << "(";
	  (*j)->prop->write(out);
	  out << "_time_" << time << ")";
	  out << ")";	  	  
	}
	for(pc_list<simple_effect*>::iterator j = my_del_effects.begin();
	    j != my_del_effects.end(); j++){
	  (*j)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
	  
	  out << "(=> ("
	      << name << "_end_time_" << (k-1) << ") ";
	  out << "(not (";
	  (*j)->prop->write(out);
	  out << "_time_" << time << ")";
	  out << "))";	  	  
	}

	for(pc_list<assignment*>::iterator j = my_assign_effects.begin();
	    j != my_assign_effects.end(); j++){
	  if((*j)->getOp() == VAL::E_ASSIGN){
	    (*j)->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
	  
	    out << "(=> ("
		<< name << "_end_time_" << (k-1) << ") ";
	    out << "(= (";
	    (*j)->getFTerm()->write(out);
	    out << "_time_" << time << ")";
	    out << ")";
	    trans(my_analysis, (*j)->getExpr(), grounding, (k-1), out);
	    out << ")";
	  } else if((*j)->getOp() == VAL::E_INCREASE || (*j)->getOp() == VAL::E_DECREASE ){
	    out << "\n// At-Start Increase Effects\n";
	    out << "(=> ("
		<< name << "_end_time_" << (k-1) << ") ";
	    out << "(" << ((*j)->getOp() == VAL::E_INCREASE ? "+" : "-") << "= (delta_" << name << "_";
	    (*j)->getFTerm()->write(out);
	    out << "_time_" << (k-1) << ")";
	  
	    trans(my_analysis, (*j)->getExpr(), grounding, (k-1), out);
	    out << ")";
	    out << ")";
	  }
	}
      }
    } else if ((*i)->ts == VAL::E_CONTINUOUS){
      for(pc_list<assignment*>::iterator j = my_assign_effects.begin();
	  j != my_assign_effects.end(); j++){

	out << "\n// Continuous Effects\n";
	out << "(=> (and (or ("
	    << name << "_start_time_" << time << ")";
	if(time > 0) { 
	  out << "(" << name << "_cont_time_" << time << ")";
	}
	out << ") (or ";
	if(time+1  < FLAGS_num_happenings) { 
	  out << "(" << name << "_cont_time_" << (time+1) << ") ";
	}
	out << "("  << name << "_end_time_" << (time+1) << "))) ";
	out << "(= (gamma_" << name << "_";
	(*j)->getFTerm()->write(out);
	out << "_time_" << time  << ") ";
	//out << "(";

	std::stringstream nm;
	//nm <<  "gamma_" << name << "_";
	(*j)->getFTerm()->write(nm);
	//nm << "_t" << time << "_t_" << (time+1);
	string snm = nm.str();
	//	  string *scp = new string(snm);
	set<string> *influences = fcontinuousers[snm];
	if(influences == NULL){
	  influences = new set<string>();
	  fcontinuousers[snm] = influences;
	}
	influences->insert(name);

	VAL::mul_expression *my_mul_expression;
	if (my_mul_expression = dynamic_cast<VAL::mul_expression*>((*j)->getExpr())){ // is (* #t f)
	  VAL::special_val_expr* hasht;
	  if(hasht = dynamic_cast< VAL::special_val_expr*>(my_mul_expression->getLHS())){
	    trans(my_analysis, my_mul_expression->getRHS(), grounding, time, out);   
	  } else if (hasht = dynamic_cast< VAL::special_val_expr*>(my_mul_expression->getRHS())){
	    trans(my_analysis, my_mul_expression->getLHS(), grounding, time, out);   
	  } 
	} else { //is #t
	  out << "1";
	}
	out << "))";


      }
    }
    
  }


  // if(effect_types[at_start_increase_index]){
  // out << "\n// At-Start Increase Effects\n";
  // }
  // if(effect_types[at_end_increase_index]){
  // out << "\n// At-End Increase Effects\n";
  // }
  // if(effect_types[continuous_index]){
  // out << "\n// Continuous Effects\n";
  // }
}

void translate::trans(VAL::analysis* my_analysis, VAL::expression *my_expression, param_grounding* grounding, int time, std::iostream& out){
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
    trans(my_analysis, my_plus_expression->getLHS(), grounding, time, out);
    out << " ";
    trans(my_analysis, my_plus_expression->getRHS(), grounding, time, out);
    out << ")";
  } else if (my_minus_expression = dynamic_cast<VAL::minus_expression*>(my_expression)){
    out << "(- ";
    trans(my_analysis, my_minus_expression->getLHS(), grounding, time, out);
    out << " ";
    trans(my_analysis, my_minus_expression->getRHS(), grounding, time, out);
    out << ")";
  } else if (my_mul_expression = dynamic_cast<VAL::mul_expression*>(my_expression)){
    out << "(* ";
    trans(my_analysis, my_mul_expression->getLHS(), grounding, time, out);
    out << " ";
    trans(my_analysis, my_mul_expression->getRHS(), grounding, time, out);
    out << ")";
  } else if (my_div_expression = dynamic_cast<VAL::div_expression*>(my_expression)){
    out << "(/ ";
    trans(my_analysis, my_div_expression->getLHS(), grounding, time, out);
    out << " ";
    trans(my_analysis, my_div_expression->getRHS(), grounding, time, out);
    out << ")";
  } else if (my_uminus_expression = dynamic_cast<VAL::uminus_expression*>(my_expression)){
    out << "(- ";
    trans(my_analysis, my_uminus_expression->getExpr(), grounding, time, out);
    out << ")";
  } else if (my_int_expression = dynamic_cast<VAL::int_expression*>(my_expression)){
    out << my_int_expression->double_value();
  } else if (my_float_expression = dynamic_cast<VAL::float_expression*>(my_expression)){
    out << my_float_expression->double_value();
  } else if (my_func_term = dynamic_cast<VAL::func_term*>(my_expression)){
    my_func_term->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    my_func_term->write(out);   
  } else if (my_class_func_term = dynamic_cast<VAL::class_func_term*>(my_expression)){
    my_class_func_term->setWriteController((auto_ptr<WriteController>)getWriteController(grounding));
    my_class_func_term->write(out);
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
