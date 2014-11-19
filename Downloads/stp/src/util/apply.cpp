// Parses, runs constant bit propagation, then outputs the result.

#include "../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../AST/AST.h"
#include "../printer/printers.h"

#include "../STPManager/STPManager.h"
#include "../to-sat/AIG/ToSATAIG.h"
#include "../sat/MinisatCore.h"
#include "../STPManager/STP.h"
#include "../cpp_interface/cpp_interface.h"

using namespace simplifier::constantBitP;

int
main(int argc, char ** argv)
{
  extern int
  smt2parse();
  extern int
  smt2lex_destroy(void);
  extern FILE *smt2in;

  BEEV::STPMgr stp;
  STPMgr * mgr = &stp;

  Cpp_interface interface(*mgr, mgr->defaultNodeFactory);
  interface.startup();
  interface.ignoreCheckSat();
  BEEV::parserInterface = &interface;

  Simplifier *simp = new Simplifier(mgr);
  ArrayTransformer * at = new ArrayTransformer(mgr, simp);
  AbsRefine_CounterExample* abs = new AbsRefine_CounterExample(mgr, simp, at);
  ToSATAIG* tosat = new ToSATAIG(mgr,at);

  GlobalSTP = new STP(mgr, simp, at, tosat, abs);

  srand(time(NULL));
  BEEV::ParserBM = &stp;

  stp.UserFlags.disableSimplifications();
  stp.UserFlags.bitConstantProp_flag = true;

  // Parse SMTLIB2-----------------------------------------
  mgr->GetRunTimes()->start(RunTimes::Parsing);
  if (argc > 1)
    {
    smt2in = fopen(argv[1], "r");
    smt2parse();
    }
  else
    {
    smt2in = NULL; // from stdin.
    smt2parse();
    }
  smt2lex_destroy();
  //-----------------------------------------------------

  ASTNode n;

  ASTVec v = interface.GetAsserts();
  if (v.size() > 1)
    n = interface.CreateNode(AND, v);
  else
    n = v[0];

  // Apply cbitp ----------------------------------------
  simplifier::constantBitP::ConstantBitPropagation cb(simp, mgr->defaultNodeFactory, n);
  if (cb.isUnsatisfiable())
    n = mgr->ASTFalse;
  else
    n = cb.topLevelBothWays(n, true, true);

  if (simp->hasUnappliedSubstitutions())
    {
    n = simp->applySubstitutionMap(n);
    simp->haveAppliedSubstitutionMap();
    }

  // Print back out.
  printer::SMTLIB2_PrintBack(cout, n);
  cout << "(check-sat)\n";
  cout << "(exit)\n";
  return 0;
}

