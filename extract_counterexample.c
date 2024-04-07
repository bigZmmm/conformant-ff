#include "ff.h"

#include "memory.h"
#include "output.h"

#include "parse.h"

#include "inst_pre.h"
#include "inst_easy.h"
#include "inst_hard.h"
#include "inst_final.h"

#include "relax.h"
#include "state_transitions.h"
#include "repeated_states.h"
#include "search.h"
#include "extract_counterexample.h"


#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>
#include <stdio.h>
#include"z3.h"





Bool conputerCounter(){
  int i,j;
  Bool success=FALSE;
  PredicateString *predicate_string;
  





  for ( i = 0; i < gnum_plan_ops; i++ ) {
    printf("%d: ", i);
    print_op_name( gplan_ops[i] );
    int index = gplan_ops[i];
    Action *a = gop_conn[index].action;
    ActionEffect *ac = a->effects;
    int* add = ac->adds;
    int* del = ac->dels;
    printf("\nadd:\n");
    for(j=0;j<ac->num_adds;j++)
      print_Fact(&(grelevant_facts[add[j]]));
    printf("\ndel:\n");
    for(j=0;j<ac->num_dels;j++)
      print_Fact(&(grelevant_facts[del[j]]));

    printf("\n     ");
  }
  return success;
}

