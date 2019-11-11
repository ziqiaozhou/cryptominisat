#include "count.h"
int main(int argc, char **argv) {
  srand(time(NULL));
  Count Count(argc, argv);
  Count.conf.verbStats = 0;
  Count.conf.preprocess = 0;
  Count.conf.restart_first = 1000000;
  Count.conf.keep_symbol = 1;
  Count.conf.simplified_cnf = ".simpfile.cnf";
  // Count.conf.doRenumberVars = true;
  Count.parseCommandLine();
  Count.run();
}
