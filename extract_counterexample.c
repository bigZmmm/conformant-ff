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

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <memory.h>
#include <setjmp.h>

#include "z3.h"
#include "set.h"

bool inFacts(int *nums,int n,int index){
  int i;
  for(i=0;i<n;i++){
    if(index==nums[i]){
      return true;
    }
  }
    
      
  return false;
}

char* itoa(int num,char* str,int radix)
{
    char index[]="0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ";
    unsigned unum;
    int i=0,j,k;
    if(radix==10&&num<0)
    {
        unum=(unsigned)-num;
        str[i++]='-';
    }
    else unum=(unsigned)num;
 
    do
    {
        str[i++]=index[unum%(unsigned)radix];
        unum/=radix;
 
    }while(unum);
 
    str[i]='\0';
 

    if(str[0]=='-') k=1;
    else k=0;
 
    char temp;
    for(j=k;j<=(i-1)/2;j++)
    {
        temp=str[j];
        str[j]=str[i-1+k-j];
        str[i-1+k-j]=temp;
    }
 
    return str;
 
}

void expandString(char* cur,int n){
  cur = (char *)realloc(cur, strlen(cur)+n);
}

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
    int total_length = strlen(add) + strlen(now)+2;
    char *new_var = (char*)calloc(total_length,sizeof(char));
    strcat(new_var,now);
    strcat(new_var," ");
    strcat(new_var,add);
    /*printf("\n%s\n",new_var);*/
    return new_var;
}

char* toSmtVariableString(char *now,int timestep){
  char *str=(char *)calloc(20,sizeof(char));
  itoa(timestep,str,10);
  int oldlen = strlen(now);
  char *new_var = (char *)calloc(oldlen+strlen(str)+2,sizeof(char) );
  strcpy(new_var,now);
  strcat(new_var,"-");
  strcat(new_var,str);
  free(now);
  free(str);
  return new_var;
}

void addAction2Goal(char *simulation,int current_goal_fact,Action *a,int new_len,SimpleSet *regre_variable,int *new_goal,int timestep){
    
    print_ft_name(current_goal_fact);
    
    int i,e;
    char *fact2string = toSmtVariableString(Fact2SmtString(current_goal_fact),timestep);
    char *cur =  toSmtVariableString(Fact2SmtString(current_goal_fact),timestep-1);
    char *pre = (char*)calloc(1,sizeof("(= ")+strlen(fact2string)+5);
    char *to_smt = (char*)calloc(1,sizeof("(OR "));
    char *add_to_string = (char*)calloc(1,sizeof("(OR FALSE "));
    char *notdel_to_string = (char*)calloc(1,sizeof("(NOT (OR FALSE "));
    strcat(to_smt,"(OR");
    strcat(add_to_string,"(OR FALSE");
    strcat(notdel_to_string,"(NOT (OR FALSE");
    strcat(pre,"(= ");
    strcat(pre,fact2string);
    
    for(e=0;e<(a->num_effects);e++){
      ActionEffect ac = a->effects[e];
      /*生成add的smt*/
      /*success*/
      if(inFacts(ac.adds,ac.num_adds,current_goal_fact)){
        if ((ac.num_conditions) > 0){
          if ((ac.num_conditions) > 1){
            add_to_string=contactString(add_to_string, "(AND");
            for (i = 0; i < ac.num_conditions; i++){
              char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[i]),timestep-1);
              /*添加新的变量*/
              /*set_add(&regre_variable, tmp);*/
              add_to_string=contactString(add_to_string, tmp);
            }
          }
          else{printf("\n1111111112%d\n",ac.conditions[0]);
            char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[0]), timestep-1);
            printf("\n%s",tmp);
            /*添加新的变量*/
            /*set_add(&regre_variable, tmp);*/
            add_to_string=contactString(add_to_string, tmp);
          }
        }else{
          add_to_string=contactString(add_to_string, "TRUE");
        }
      /*生成del的smt*/
      }else if(inFacts(ac.dels,ac.num_dels,current_goal_fact)){
        if((ac.num_conditions)>0){
          if((ac.num_conditions)>1){
              notdel_to_string=contactString(notdel_to_string,"(AND");
              for(i=0;i<ac.num_conditions;i++){
                char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[i]),timestep-1);
                /*添加新的变量*/
                set_add(&regre_variable, tmp);
                notdel_to_string=contactString(notdel_to_string,tmp);
              }
          }else{
            char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[0]),timestep-1);
            /*添加新的变量*/
            set_add(&regre_variable, tmp);
            notdel_to_string=contactString(notdel_to_string,tmp);
          }
        }else{
          notdel_to_string=contactString(notdel_to_string, "TRUE");
        }
      }
    }
    
    add_to_string= contactString(add_to_string, ")");
    notdel_to_string= contactString(notdel_to_string,") )");

    to_smt = contactString(to_smt,"(AND");
    to_smt = contactString(to_smt,notdel_to_string);
    to_smt = contactString(to_smt,add_to_string);
    to_smt = contactString(to_smt,")");
    to_smt = contactString(to_smt,"(AND");
    to_smt = contactString(to_smt,cur);
    to_smt = contactString(to_smt,notdel_to_string);
    to_smt = contactString(to_smt,") )");
    pre = contactString(pre,to_smt);
    pre = contactString(pre,")");
    /*printf("\n%s\n",simulation);*/
    
    simulation = contactString(simulation,pre);
    
    free(fact2string);
    free(cur);
    free(pre);
    free(to_smt);
    free(add_to_string);
    free(notdel_to_string);
    printf("\n: %s \n",simulation);
    
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
  /*存储当前的目标状态谓语*/  /*一*/
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

  /*当前目标状态ggoal_state
  对目标状态进行回归*/
  SimpleSet regre_variable;
  int new_goal[10000];
  for (i = timestep-1; i >=0; i--)
  {
      printf("\n%d :",i);
      print_op_name( gplan_ops[i] );
      Action *a = gop_conn[gplan_ops[i]].action;
      int new_len=0;
      for(j=0;j<goal_len;j++){
          printf("\n%s\n",simulation);
          addAction2Goal(simulation,current_goal_fact[j],a,&new_len,&regre_variable,new_goal,i+1);
      }
      /*goal_len = new_len;*/
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