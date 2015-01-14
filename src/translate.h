#pragma once

#include "val/main.h"
#include "val/State.h"
#include "val/Plan.h"
#include "val/Validator.h"
#include "val/typecheck.h"
#include "val/RobustAnalyse.h"
#include "val/ptree.h"
#include "val/FlexLexer.h"
#include "val/Utils.h"
#include <fstream>
#include "smtWriteController.h"



typedef map<string, set<string>*> fassignmentmap;
typedef fassignmentmap fincrementmap;
typedef fassignmentmap fdecrementmap;
typedef fassignmentmap fcontinuousmap;

typedef map<string, list<string>*> passignmentmap;


class translate {
 public:
 translate()  { }
  ~translate() {}
  void translateSMT(VAL::analysis* my_analysis);
  VAL::smtWriteController* getWriteController(param_grounding *grounding)  { 
    wcnt.setGrounding(grounding); 
    return &wcnt; 
  }
  std::string getTimepoint(double t); 


 private:
  VAL::smtWriteController wcnt;
  timemap timepoints;

  fassignmentmap fassigners;
  fincrementmap fincrementers;
  fdecrementmap fdecrementers;
  fcontinuousmap fcontinuousers;
  
  set<string> functions;

  void get_precond_types(bool* types, VAL::goal* goal);
  void get_effect_types(bool* types, VAL::effect_lists* eff);
  void trans(VAL::analysis* my_analysis, 
		 VAL::effect_lists *effects, 
	     param_grounding *grounding,
		 int time, 
		 std::iostream& out);
  void trans(VAL::analysis* my_analysis, 
	     VAL::goal *goal,
	     param_grounding* grounding,
	     int start_time, 
	     int end_time, 
	     std::iostream& out);
  void trans(VAL::analysis* my_analysis, 
	     VAL::durative_action *my_durative_action,
	     param_grounding *grounding,
	     int time, 
	     std::iostream& out);
  void trans(const VAL::comparison_op op, std::iostream& out);
  void trans_duration_comparison(VAL::analysis* my_analysis, 
				 VAL::comparison *my_comparison,
				 VAL::operator_* my_operator,
				 param_grounding* grounding, 
				 int act_time, 
				 int dur_time, 
				 std::iostream& out);
  void trans(VAL::analysis* my_analysis, 
	     VAL::expression *my_expression,
	     param_grounding* grounding, 
	     int time, 
	     std::iostream& out);
  std::list<param_grounding*>* get_groundings(VAL::var_symbol_list* symbols, list<VAL::const_symbol*> *constants);
  std::list<param_grounding*>* get_groundings_rec(VAL::var_symbol_list* symbols, list<VAL::const_symbol*> *constants, std::list<param_grounding*>*groundings, param_grounding* current_grounding, VAL::var_symbol_list::iterator parameters);


};
