#ifndef __GETOPT_H_INCLUDED_
#define __GETOPT_H_INCLUDED_
//
//  akpo_getopt.h  -  renamed to avoid clash with other getopt.h includes
//

extern int ac_opterr;      /* if error message should be printed */
extern int ak_optind;      /* index into parent argv vector */
extern int ak_optopt;      /* character checked for validity */
extern int ak_optreset;        /* reset getopt */
extern char* ak_optarg;        /* argument associated with option */

struct option {
    const char* name;
    int has_arg;
    int* flag;
    int val;
};


#define no_argument       0
#define required_argument 1
#define optional_argument 2

int getopt(int, char**, char*);
int getopt_long(int, char**, const char*, struct option*, int*);

#endif /* __GETOPT_H_INCLUDED_ */
