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

typedef std::map<double, std::string> timemap;
typedef std::map<VAL::var_symbol*, VAL::const_symbol*> param_grounding;

class translate {
 public:
 translate()  { }
  ~translate() {}
  void translateSMT(VAL::analysis* my_analysis);
  VAL::smtWriteController* getWriteController()  { return &wcnt; }
  std::string getTimepoint(double t); 


 private:
  VAL::smtWriteController wcnt;
  timemap timepoints;
  
  void trans(VAL::analysis* my_analysis, 
		 VAL::effect_lists *effects, 
		 int time, 
		 std::ofstream& out);
  void trans(VAL::analysis* my_analysis, 
		 VAL::goal *goal,
		 int start_time, 
		 int end_time, 
		 std::ofstream& out);
  void trans(VAL::analysis* my_analysis, 
		 VAL::durative_action *my_durative_action,
		 int time, 
		 std::ofstream& out);
  void trans(const VAL::comparison_op op, std::ofstream& out);
  void trans_duration_comparison(VAL::analysis* my_analysis, 
				 VAL::comparison *my_comparison,
				 VAL::operator_* my_operator,
				 int act_time, 
				 int dur_time, 
				 std::ofstream& out);
  void trans(VAL::analysis* my_analysis, 
	     VAL::expression *my_expression,
	     int time, 
	     std::ofstream& out);
  std::list<param_grounding*>* get_groundings(VAL::operator_ *op, list<VAL::const_symbol*> *constants);
};
