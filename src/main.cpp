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

#include "version.h"
#include <cstdlib>
#include <cstdio>
#include <csignal>
#include <iostream>
#include <string>
#include <assert.h>
#include <glog/logging.h>
#include <gflags/gflags.h>
#include "util/git_sha1.h"

#include "val/State.h"
#include "val/Plan.h"
#include "val/Validator.h"
#include "val/typecheck.h"
#include "val/RobustAnalyse.h"

#include <fstream>
#include <time.h>
#include "val/ptree.h"
#include "val/FlexLexer.h"
#include "val/Utils.h"

//#include "val/LaTeXSupport.h"
#include "val/main.h"

#include "translate.h"

using std::ifstream;
using std::ofstream;
using std::cerr;
using std::cout;
using std::for_each;
using std::copy;


#if defined(__linux__)
#include <fpu_control.h>
#endif

using std::stringstream;
void        catcher            ( int );
bool stop;


DEFINE_string(domain, "", "Domain File");
DEFINE_string(problem, "", "Problem File");


extern int yyparse();
extern int yydebug;

namespace VAL {

parse_category* top_thing = NULL;

analysis an_analysis;
analysis* current_analysis;

yyFlexLexer* yfl;
int Silent;
int errorCount;
bool Verbose;
bool ContinueAnyway;
bool ErrorReport;
bool InvariantWarnings;
bool LaTeX;

ostream * report = &cout;


};

char * current_filename;

/*****************************************************************************\
 *                                                                           *
 *                                  MAIN                                     *
 *                                                                           *
\*****************************************************************************/

int main( int argc, char * argv[] )
{
  // Init Google Logging
  google::InitGoogleLogging(argv[0]);

  // Set up version, usage message
  stringstream ss;
  ss << PACKAGE_VERSION
     << " (commit " << std::string(preal::getGitSHA1()).substr(0, 12) << ")";
  gflags::SetVersionString(ss.str());
  gflags::SetUsageMessage(argv[0]);
  FLAGS_logtostderr = 1;
  // Parse cmd-line, it will update argc and argv
  gflags::ParseCommandLineFlags(&argc, &argv, true);

  // Catch SigTerm, so that it answers even on ctrl-c
  signal( SIGTERM, catcher );
  signal( SIGINT , catcher );

  LOG(INFO) << "Domain File: " << FLAGS_domain;
  LOG(INFO) << "Problem File: " << FLAGS_problem;

  VAL::current_analysis= &VAL::an_analysis;
  //an_analysis.const_tab.symbol_put(""); //for events - undefined symbol
  VAL::Silent = 0;
  VAL::errorCount = 0;
  VAL::ContinueAnyway = false;
  VAL::ErrorReport = false;
  VAL::Robust = false;
  VAL::JudderPNEs = false;
  VAL::EventPNEJuddering = false;
  VAL::TestingPNERobustness = false;
  VAL::RobustPNEJudder = 0;
  bool CheckDPs = true;
  VAL::Verbose = true;
  
   ifstream domainFile((string)FLAGS_domain);
    if(!domainFile)
    {
      LOG(ERROR) << "Bad domain file!\n";
	//    	if(LaTeX) *report << "\\section{Error!} Bad domain file! \n \\end{document}\n";
    	exit(-1);
    };

    VAL::yfl= new yyFlexLexer(&domainFile,&LOG(INFO));

    yydebug=0;
    LOG(INFO) << "Parsing Domain ...";
    yyparse();
    LOG(INFO) << "Parsed Domain ...";
    delete VAL::yfl;

    if(!VAL::an_analysis.the_domain)
    {
    	LOG(ERROR) << "Problem in domain definition!\n";
	//    	if(LaTeX) *report << "\\section{Error!} Problem in domain definition! \n \\end{document}\n";
    	exit(-1);
    };

    VAL::TypeChecker tc(VAL::current_analysis);

    //	if(LaTeX) Verbose = false;
    bool typesOK = tc.typecheckDomain();

    //    if(LaTeX) Verbose = true;

    if(!typesOK)
    {
    	LOG(ERROR)  << "Type problem in domain description!\n";

    	// if(LaTeX)
    	// {
    	// 	*report << "\\section{Error!} Type problem in domain description! \n \\begin{verbatim}";
    	// 	tc.typecheckDomain();
    	// 	*report << "\\end{verbatim} \\end{document}\n";
    	// };


    	exit(-1);
    };



    ifstream problemFile(FLAGS_problem);
    if(!problemFile)
    {
    	LOG(ERROR)  << "Bad problem file!\n";
	//    	if(LaTeX) *report << "\\section{Error!} Bad problem file! \n \\end{document}\n";
    	exit(-1);
    };
    LOG(INFO) << "Parsing Problem ...";
    VAL::yfl = new yyFlexLexer(&problemFile,&cout);
    yyparse();
    LOG(INFO) << "Parsed Problem ...";
    delete VAL::yfl;

	if(!tc.typecheckProblem())
	{
		LOG(ERROR)  << "Type problem in problem specification!\n";
		//		if(LaTeX) *report << "\\section{Error!} Type problem in problem specification!\n \\end{document}\n";
		exit(-1);
	};


      // 	if(LaTeX)
      // 	{
      // latex.LaTeXDomainAndProblem();
      // 	};



	const VAL::DerivationRules * derivRules = new VAL::DerivationRules (VAL::an_analysis.the_domain->drvs,VAL::an_analysis.the_domain->ops);

	if(CheckDPs && !derivRules->checkDerivedPredicates())
	{
	  //		if(LaTeX) latex.LaTeXEnd();
		exit(-1);

	};

	translate tr;
	tr.translateSMT(VAL::current_analysis);
	
	LOG(INFO) << "Exiting";
	return 0;
}



void catcher( int sig )
{
  LOG(INFO) << "Received Signal: " << sig;
  switch (sig)
  {
    case SIGINT:
    case SIGTERM:
      if ( stop )
      {
        //parser_ctx->PrintResult( l_Undef );
        exit( 1 );
      }
      stop = true;
      break;
  }
}

