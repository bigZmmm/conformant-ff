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

#include <stdlib.h>
#include <stdarg.h>
#include <memory.h>
#include <setjmp.h>
#include <stdio.h>
#include "z3.h"
#include "set.h"

char *Fact2SmtString(int i)
{
  char *name,tmp[1000]={0};
  int j;
  Fact *f = &(grelevant_facts[i]);
  sprintf(tmp, gpredicates[f->predicate]);
  for (j = 0; j < garity[f->predicate]; j++)
  {
    if (f->args[j] >= 0)
    {
      sprintf(tmp+strlen(tmp), gconstants[(f->args)[j]]);
    }
    else
    {
      sprintf(tmp+strlen(tmp), DECODE_VAR(f->args[j]));
    }
  }
  /*printf("\n%s\n",tmp);*/
  name = (char *)malloc(strlen(tmp) + 1);
  strcpy(name, tmp);
  return name;
}

char* contactString(char *now,char *add){
    int total_length = strlen(add) + strlen(now)+1;
    now = (char *)realloc(now, total_length);
    strcat(now, add);
    strcat(now," ");
    char *new_var = calloc(total_length,sizeof(char));
    strcpy(new_var,now);
    free(add);
    free(now);
    printf("\n%s\n",new_var);
    return new_var;
}

char* toSmtVariableString(char *now,int timestep){
  char str[20]={0}; // 假设要转换的数字不超过 20 个字符的长度
  str[0]='-';
  sprintf(str+1, "%d", timestep);
  int oldlen = strlen(now);
  char *new_var = (char *)calloc(oldlen+strlen(str),sizeof(char) );
  strcpy(new_var,now);
  strcat(new_var,str);
  free(now);
  return new_var;
}

Bool conputerCounter()
{
  int i, j;
  Bool success = FALSE;
  PredicateString *predicate_string;
  char *simulation = (char *)calloc(1, sizeof("(assert (and true "));
  strcat(simulation,"(assert (and true ");
  char *preference = (char *)calloc(1, sizeof("(not (and "));
  strcat(preference,"(not (and ");
  SimpleSet variables;
  set_init(&variables);

  /*添加所有初始状态谓语*/
  for (i = 0; i < ginitial_state.num_F; i++)
  {
    set_add(&variables, Fact2SmtString(ginitial_state.F[i]));
  }
  for (i = 0; i < ginitial_state.num_U; i++)
  {
    set_add(&variables, Fact2SmtString(ginitial_state.U[i]));
  }
  
  /* 测试variavles的导入
  uint64_t length=set_length(&variables);
  char** tmp = set_to_array(&variables,&length);
  printf("\nlength: %d",length);
  printf("\n");
  for(i=0;i<length;i++){
    printf("%s_%d ",tmp[i],strlen(tmp[i]));
  }
  printf("\n");
  */
 
  /*
    根据plan对目标状态所有的谓语进行回溯，过程中每步的表示都要按照步数进行标注
    一、对目标的所有谓语进行，添加-timestep ——> preference
    二、对目标状态进行回归，（= 当前目标状态~第一次动作后的状态的谓语 【c isvalid true】【c isunsatisfied false】【c-timestep】 )
    三、回归中动作不为空的前置条件的所有谓语-timestep
  
  */
  int timestep = gnum_plan_ops;
  /*存储当前的目标状态谓语*/
  int goal_len=ggoal_state.num_F+ggoal_state.num_U;
  int *current_goal_fact=(int *)calloc(goal_len, sizeof(int));
  for(i=0;i<ggoal_state.num_F;i++){
    current_goal_fact[i]=ggoal_state.F[i];
    preference=contactString(preference,toSmtVariableString(Fact2SmtString(ggoal_state.F[i]),timestep));
  }
  for(i=0;i<ggoal_state.num_U;i++){
    current_goal_fact[ggoal_state.num_F+i]=ggoal_state.U[i];
    preference=contactString(preference,toSmtVariableString(Fact2SmtString(ggoal_state.U[i]),timestep));
  }

  /*一*/
  printf("\n%s %d\n",preference,strlen(preference));

  

  /*当前目标状态ggoal_state*/
  {
    
    for (i = timestep; i > 0; i--)
    {


    }
  }

  /*
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
  */
  return success;
}