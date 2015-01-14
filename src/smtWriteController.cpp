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

#include "smtWriteController.h"

namespace VAL {

void smtWriteController::write_symbol(ostream & o,const symbol * p)
{
  //p->display(indent);
  o << p->getName();
};

void smtWriteController::write_const_symbol(ostream & o,const const_symbol * p)
{
	o << p->getName();
};

void smtWriteController::write_class_symbol(ostream & o,const class_symbol * p)
{
  //p->display(indent);
o << p->getName();
};

void smtWriteController::write_var_symbol(ostream & o,const var_symbol * p)
{
  //	p->display(indent);
  o << p->getName();
};

void smtWriteController::write_pddl_typed_symbol(ostream & o,const pddl_typed_symbol * p)
{
	o << p->getName();
};

void smtWriteController::write_plus_expression(ostream & o,const plus_expression * p)
{
	p->display(indent);
};

void smtWriteController::write_minus_expression(ostream & o,const minus_expression * p)
{
	p->display(indent);
};

void smtWriteController::write_mul_expression(ostream & o,const mul_expression * p)
{
	p->display(indent);
};

void smtWriteController::write_div_expression(ostream & o,const div_expression * p)
{
	p->display(indent);
};

void smtWriteController::write_uminus_expression(ostream & o,const uminus_expression * p)
{
	p->display(indent);
};

void smtWriteController::write_int_expression(ostream & o,const int_expression * p)
{
  //p->display(indent);
  o << p->double_value();
};

void smtWriteController::write_float_expression(ostream & o,const float_expression * p)
{
  //p->display(indent);
  o << p->double_value();
};

void smtWriteController::write_special_val_expr(ostream & o,const special_val_expr * p)
{
	p->display(indent);
};

void smtWriteController::write_func_term(ostream & o,const func_term * p)
{
  //p->display(indent);
  p->getFunction()->write(o);
  for(parameter_symbol_list::const_iterator i = p->getArgs()->begin();i != p->getArgs()->end();++i){
    o << "_";
    if(grounding == NULL){
      (*i)->write(o);
    }
    else{
      for(param_grounding::iterator j = grounding->begin(); j != grounding->end();++j){
	if((*j).first == *i){
	  (*j).second->write(o);
	  break;
	}
      }
    }
  }
};

void smtWriteController::write_class_func_term(ostream & o,const class_func_term * p)
{
	p->display(indent);
};

void smtWriteController::write_assignment(ostream & o,const assignment * p)
{
	p->display(indent);
};

void smtWriteController::write_goal_list(ostream & o,const goal_list * p)
{
	p->display(indent);
};

void smtWriteController::write_simple_goal(ostream & o,const simple_goal * p)
{
  p->getProp()->write(o);
};

void smtWriteController::write_qfied_goal(ostream & o,const qfied_goal * p)
{
	p->display(indent);
};

void smtWriteController::write_conj_goal(ostream & o,const conj_goal * p)
{
	p->display(indent);
};

void smtWriteController::write_disj_goal(ostream & o,const disj_goal * p)
{
	p->display(indent);
};

void smtWriteController::write_timed_goal(ostream & o,const timed_goal * p)
{
	p->display(indent);
};

void smtWriteController::write_imply_goal(ostream & o,const imply_goal * p)
{
	p->display(indent);
};

void smtWriteController::write_neg_goal(ostream & o,const neg_goal * p)
{
  p->write(o);
};

void smtWriteController::write_comparison(ostream & o,const comparison * p)
{
	p->display(indent);
};

void smtWriteController::write_proposition(ostream & o,const proposition * p)
{
  //	p->display(indent);
  p->head->write(o);
  for(parameter_symbol_list::iterator i = p->args->begin();i != p->args->end();++i){
    o << "_";
    if(grounding == NULL){
      (*i)->write(o);
    }
    else{
      for(param_grounding::iterator j = grounding->begin(); j != grounding->end();++j){
	if((*j).first == *i){
	  (*j).second->write(o);
	  break;
	}
      }
    }
  }
		
  
};

void smtWriteController::write_pred_decl_list(ostream & o,const pred_decl_list * p)
{
	p->display(indent);
};

void smtWriteController::write_func_decl_list(ostream & o,const func_decl_list * p)
{
	p->display(indent);
};

void smtWriteController::write_pred_decl(ostream & o,const pred_decl * p)
{
	p->display(indent);
};

void smtWriteController::write_func_decl(ostream & o,const func_decl * p)
{
	p->display(indent);
};

void smtWriteController::write_simple_effect(ostream & o,const simple_effect * p)
{
	p->display(indent);
};

void smtWriteController::write_forall_effect(ostream & o,const forall_effect * p)
{
	p->display(indent);
};

void smtWriteController::write_cond_effect(ostream & o,const cond_effect * p)
{
	p->display(indent);
};

void smtWriteController::write_timed_effect(ostream & o,const timed_effect * p)
{
	p->display(indent);
};

void smtWriteController::write_timed_initial_literal(ostream & o,const timed_initial_literal * p)
{
	p->display(indent);
};

void smtWriteController::write_effect_lists(ostream & o,const effect_lists * p)
{
	p->display(indent);
};

void smtWriteController::write_operator_list(ostream & o,const operator_list * p)
{
	p->display(indent);
};

void smtWriteController::write_derivations_list(ostream & o,const derivations_list * d)
{
	d->display(indent);
};

void smtWriteController::write_derivation_rule(ostream & o,const derivation_rule * d)
{
	d->display(indent);
};

void smtWriteController::write_operator_(ostream & o,const operator_ * p)
{
	p->display(indent);
};

void smtWriteController::write_action(ostream & o,const action * p)
{
	p->display(indent);
};

void smtWriteController::write_event(ostream & o,const event * p)
{
	p->display(indent);
};

void smtWriteController::write_process(ostream & o,const process * p)
{
	p->display(indent);
};

void smtWriteController::write_durative_action(ostream & o,const durative_action * p)
{
	p->display(indent);
};

void smtWriteController::write_class_def(ostream & o,const class_def * p)
{
	p->display(indent);
};

void smtWriteController::write_domain(ostream & o,const domain * p)
{
	p->display(indent);
};

void smtWriteController::write_metric_spec(ostream & o,const metric_spec * p)
{
	p->display(indent);
};

void smtWriteController::write_length_spec(ostream & o,const length_spec * p)
{
	p->display(indent);
};

void smtWriteController::write_problem(ostream & o,const problem * p)
{
	p->display(indent);
};

void smtWriteController::write_plan_step(ostream & o,const plan_step * p)
{
	p->display(indent);
};

void smtWriteController::write_preference(ostream & o,const preference * p)
{
	p->display(indent);
};

void smtWriteController::write_constraint_goal(ostream & o,const constraint_goal * cg)
{
	cg->display(indent);
};

void smtWriteController::write_violation_term(ostream & o,const violation_term * vt)
{
	vt->display(indent);
};

};

