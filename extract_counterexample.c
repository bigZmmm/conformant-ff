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

/*对具有相对真值的谓语添加约束*/
char* neg_assert;

/*装换大写为小写*/
void toLower(char* str){
  int len = strlen(str);
  int i;
  for(i=0;i<len;i++){
    if(str[i]>=65&&str[i]<=90)
      str[i] = str[i]+32;
  }
}

/*判断index对应的fact是否在add集或在del集合中，其中nums是add集/del集合 n为add集/del集合的长度*/
bool inFacts(int *nums,int n,int index){
  int i;
  for(i=0;i<n;i++){
    if(index==nums[i]){
      return true;
    }
  }   
  return false;
}

/*Z3*/
void error_handler(Z3_context c, Z3_error_code e)
{
    printf("Error code: %d\n", e);
    printf("incorrect use of Z3\n");
}

Z3_solver mk_solver(Z3_context ctx)
{
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  return s;
}

Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err)
{
    Z3_context ctx;

    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);

    return ctx;
}

Z3_context mk_context()
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

/*end-Z3*/

/*提取最后一个数字，代表着plan的步数*/
int extractFinalNum(char *var){
  // printf("\nvar: %s",var);
  int num=0,ten=1,len=strlen(var),i;
  for(i=len-1;i>=0;i--){
    if(var[i]=='-')
      break;
    num = ten*(var[i]-48)+ num;
    ten*=10;
  }
  return num;
}

/*提取倒数第二个数字，代表着fact的下标*/
int extractFinalSeconNum(char *var){
  int num=0,ten=1,len=strlen(var),i;
  while(var[len-1]!='-'){
    len--;
  }
  len--;
  for(i=len-1;i>=0;i--){
    if(var[i]=='-')
      break;
    num = ten*(var[i]-48)+ num;
    ten*=10;
  }
  return num;
}

/*连接now（第一个参数）和add（第二个参数），并返回一个新的字符串替换now*/
char* contactString(char *now,char *add){
    int total_length = strlen(add) + strlen(now)+2;
    char *new_var = (char*)calloc(total_length,sizeof(char));
    strcat(new_var,now);
    strcat(new_var," ");
    strcat(new_var,add);
    free(now);
    /*printf("\n%s\n",new_var);*/
    return new_var;
}

/*装换数字num为一个字符串，保存在str中，如果num为负数，会在前添加一个负号*/
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

/*返回一个 fact转换为smt变量的字符串（未添加timestep），在最后通过-连接fact的index下标，以便于后续提取反例*/
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
  name = (char *)calloc(strlen(tmp) + 1+10,sizeof(char));
  strcpy(name, tmp);
  char *fact_num = (char*)calloc(20,sizeof(char));
  itoa(i,fact_num,10);
  strcat(name,"-");
  strcat(name,fact_num);
  return name;
}

/*更新最新的目标表，设置newgoal中的下标index为1*/
void addToNgoal(int *newgoal,int index){
  if(newgoal[index]==0){
    newgoal[index]=1;
  }
}

/*构成最终的smt变量，添加了timestep*/
char* toSmtVariableString(char *now,int timestep){
  char *str=(char *)calloc(20,sizeof(char));
  itoa(timestep,str,10);
  int oldlen = strlen(now);
  char *new_var = (char *)calloc(oldlen+strlen(str)+2,sizeof(char) );
  strcpy(new_var,now);
  strcat(new_var,"-");
  strcat(new_var,str);
  free(str);
  free(now);
  return new_var;
}

/*对具有相对真值的fact，其约束写进到smt公式中*/
void assert_Neg(int cur_fact,int timestep,SimpleSet *regre_variable){
    /*对于timestep0去重添加*/
    if(timestep==0&&fact_unuse_zero[cur_fact]==1||neg_fact[cur_fact]==0)
      return;
    char *tmp = (char*)calloc(1,sizeof("(assert (="));
    strcat(tmp,"(assert (=");
    char *cur_var = toSmtVariableString(Fact2SmtString(cur_fact),timestep);
    /*对应neg_fact[cur_fact]-1，是因为初始化里面对应的下标要！=0，区分没有哈希到的情况*/
    char *neg_var = toSmtVariableString(Fact2SmtString(ginitial_equivalence_A[neg_fact[cur_fact]-1]),timestep);
    tmp = contactString(tmp,cur_var);
    tmp = contactString(tmp,"(not");
    tmp = contactString(tmp,neg_var);
    tmp = contactString(tmp,")))\n");
    neg_assert = contactString(neg_assert,tmp);
    /*printf("\n%s\n",tmp);*/
    /*判断这个变量是否已经添加到变量表中了*/
    if(set_add(regre_variable,neg_var)){
      free(neg_var);
    }
    free(tmp);
    if(set_add(regre_variable,cur_var)){
      free(cur_var);
    }
    if(timestep==0)
      fact_unuse_zero[cur_fact]=1;
}

/* - - 当前回溯谓语 谓语前动作 - 所有变量 下一轮回归的谓语集合 当前时间步 */
void addAction2Goal(char **simulation,char **preference,int current_goal_fact,Action *a,int new_len,SimpleSet *regre_variable,int *new_goal,int timestep){
    /*print_ft_name(current_goal_fact);*/
    
    if(strcmp(a->name,"REQUEST-COPY")==0)
      print_Action(a);
    addToNgoal(new_goal,current_goal_fact);
    int i,e;
    char *fact2string = toSmtVariableString(Fact2SmtString(current_goal_fact),timestep);
    /*为neg的fact添加相反的规则*/
    char *cur =  toSmtVariableString(Fact2SmtString(current_goal_fact),timestep-1);
    /*添加第0步的neg*/
    if((timestep-1)==0)
      assert_Neg(current_goal_fact,0,regre_variable);
    char *pre = (char*)calloc(1,sizeof("(= ")+strlen(fact2string)+5);
    char *to_smt = (char*)calloc(1,sizeof("(OR "));
    char *add_to_string = (char*)calloc(1,sizeof("(OR FALSE "));
    char *notdel_to_string = (char*)calloc(1,sizeof("(NOT (OR FALSE "));
    strcat(to_smt,"(OR");
    strcat(add_to_string,"(OR FALSE");
    strcat(notdel_to_string,"(NOT (OR FALSE");
    strcat(pre,"(= ");
    strcat(pre,fact2string);
    /*遍历该动作的所有的条件影响，将可能的前置状态都得到*/
    for(e=0;e<(a->num_effects);e++){
      ActionEffect ac = a->effects[e];
      /*生成add的smt*/
      /*当前回溯谓语在动作的add集中*/
      if(inFacts(ac.adds,ac.num_adds,current_goal_fact)){
        /*effect前置条件when不为空*/
        if ((ac.num_conditions) > 0){
          if ((ac.num_conditions) > 1){
            add_to_string=contactString(add_to_string, "(AND");
            for (i = 0; i < ac.num_conditions; i++){
              char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[i]),timestep-1);
              /*添加新的变量*/
              add_to_string=contactString(add_to_string, tmp);
              if(set_add(regre_variable, tmp)){
                free(tmp);
              }
              /*作为新的搜索fact*/
              addToNgoal(new_goal,ac.conditions[i]);
              /*如果是timestep=0，则将neg对应的谓语添加*/
              if((timestep-1)==0)
                assert_Neg(ac.conditions[i],0,regre_variable);
            }
            add_to_string=contactString(add_to_string, ")");
          }
          else{
            char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[0]), timestep-1);
            /*添加新的变量*/
            add_to_string=contactString(add_to_string, tmp);
            if(set_add(regre_variable, tmp)){
              free(tmp);
            }
            addToNgoal(new_goal,ac.conditions[0]);
            /*如果是timestep=0，则将neg对应的谓语添加*/
            if((timestep-1)==0)
              assert_Neg(ac.conditions[0],0,regre_variable);
          }
        /*没有when*/
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
                notdel_to_string=contactString(notdel_to_string,tmp);
                if(set_add(regre_variable, tmp)){
                  free(tmp);
                }
                addToNgoal(new_goal,ac.conditions[i]);
                /*如果是timestep=0，则将neg对应的谓语添加*/
                if((timestep-1)==0)
                  assert_Neg(ac.conditions[i],0,regre_variable);
              }
              notdel_to_string=contactString(notdel_to_string,")");
          }else{
            char *tmp = toSmtVariableString(Fact2SmtString(ac.conditions[0]),timestep-1);
            /*添加新的变量*/
            notdel_to_string=contactString(notdel_to_string,tmp);
            if(set_add(regre_variable, tmp)){
              free(tmp);
            }
            addToNgoal(new_goal,ac.conditions[0]);
            /*如果是timestep=0，则将neg对应的谓语添加*/
            if((timestep-1)==0)
              assert_Neg(ac.conditions[0],0,regre_variable);
          }
        }else{
          notdel_to_string=contactString(notdel_to_string, "TRUE");
        }
      }
    }
    /*如果前置条件不为空，对前置条件的谓语进行添加 其中cff前置条件与目标状态仅允许简单的合取*/
    char *precondition = (char*)calloc(10,sizeof(char));
    if(a->num_preconds>0){
       if(a->num_preconds>1){
          precondition = contactString(precondition,"(AND");
          for(i=0;i<a->num_preconds;i++){
              char *tmp = toSmtVariableString(Fact2SmtString(a->preconds[i]),timestep-1);
              precondition = contactString(precondition,tmp);
              if(set_add(regre_variable, tmp)){
                free(tmp);
              }
              addToNgoal(new_goal,a->preconds[i]);
              /*如果是timestep=0，则将neg对应的谓语添加*/
              if((timestep-1)==0)
                assert_Neg(a->preconds[i],0,regre_variable);
          }
          precondition = contactString(precondition,")\n");
       }else{
          char *tmp = toSmtVariableString(Fact2SmtString(a->preconds[0]),timestep-1);
          precondition = contactString(precondition,tmp);
          if(set_add(regre_variable, tmp)){
            free(tmp);
          }
          addToNgoal(new_goal,a->preconds[0]);
          precondition = contactString(precondition,"\n");
          /*如果是timestep=0，则将neg对应的谓语添加*/
          if((timestep-1)==0)
            assert_Neg(a->preconds[0],0,regre_variable);
       }
    }
    /*printf("\n%s\n",precondition);*/
    *preference = contactString(*preference,precondition);
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
    pre = contactString(pre,")\n");
    /*printf("\n%s\n",simulation);*/
    
    *simulation = contactString(*simulation,pre);
    if(set_add(regre_variable, fact2string)){
       free(fact2string);
    }    
    if(set_add(regre_variable, cur)){
       free(cur);
    }      
    /**/
    /**/
    free(pre);
    free(to_smt);
    free(add_to_string);
    free(notdel_to_string);
    free(precondition);
    /*printf("\n: %s \n",*simulation);*/
    
}

void updNewgoal(int *new_goal,int *current_goal_fact,int *new_len){
  int len=0;
  for(int i=0;i<10000;i++){
    if(new_goal[i]==1){
      current_goal_fact[len++]=i;
    }
  }
  *new_len = len;
}

Bool test111(int i){
  if(neg_assert==NULL){
    neg_assert = (char*)calloc(10,sizeof(char));
  }else{
    memset(neg_assert,0,strlen(neg_assert));
    realloc(neg_assert, 10);
  }
  if(i==0){
    neg_assert = contactString(neg_assert,"123");
  }else if(i==1){
    neg_assert = contactString(neg_assert,"3456789");
  }else if(i==2){
    neg_assert = contactString(neg_assert,"9");
  }else if(i==3){
    neg_assert = contactString(neg_assert,"8714124");
  }
  printf("\n%s %d %d\n",neg_assert,strlen(neg_assert),neg_assert[0]);
}


int extractCounter(Z3_context ctx,Z3_model m,int *ce){
    unsigned num_constants;
    unsigned i;
    if (!m) return;
    int celen = 0;
    num_constants = Z3_model_get_num_consts(ctx, m);
    for (i = 0; i < num_constants; i++) {
        Z3_symbol name;
        Z3_func_decl cnst = Z3_model_get_const_decl(ctx, m, i);
        Z3_ast a, v;
        bool ok;
        /*获取变量名*/
        name = Z3_get_decl_name(ctx, cnst);
        char *nowvar =(char*)calloc(1000,sizeof(char)); 
        
        strcat(nowvar,Z3_get_symbol_string(ctx, name));
        // strcat(nowvar,"not-ine1f1-1231-0");
        /*获取真值*/
        a = Z3_mk_app(ctx, cnst, 0, 0);
        v = a;
        ok = Z3_model_eval(ctx, m, a, 1, &v);
        
        char *istrue = Z3_ast_to_string(ctx,v);
        
        int step = extractFinalNum(nowvar);
        
        // printf("\n%d %s",step,istrue);
        // printf("%d\n",strcmp(istrue,"true"));
        if((strcmp(istrue,"true")==0)&&step==0){
            int factnum = extractFinalSeconNum(nowvar);
            ce[factnum]=1;
            celen++;
            // printf("\nfact:%d %d\n",factnum,celen);
        }
        // else
        //   printf("\nfalse\n");
    }
  return celen;
}

/*使ginitial_state的所有oneof和or都为空*/
void initGinitiaState(){
  int i,j;
  /*初始化ginitial_state*/
  ginitial_state.num_F = 0; 
  ginitial_state.num_U = 0;
  ginitial_state.num_unknown_E = 0;
  /*初始化or*/
  gnum_initial_or = 0;
  for (i = 0; i < gnum_initial_or_old; i++)
  {
    ginitial_or_length[i] = 0;
    memset(ginitial_or[i],0,ginitial_or_length_old[i]);
  }
  /*初始化两个是否已添加表*/
  memset(isadd2Ffact,0,10000);
  memset(isadd2Ufact,0,10000);
  /*初始化plan为空*/
  gnum_plan_ops=0;
  memset(gplan_ops,0,MAX_PLAN_LENGTH);
}

/*第i个or要添加新的进来*/
void addNewOr(int index){
  int i;
  /*如果当前需要存储的or，超出了初始化or的大小，进行扩充*/
  if(ginitial_or_length_old[gnum_initial_or]<contains_ginitial_or_length[index])
      ginitial_or[gnum_initial_or] = (int *)realloc(ginitial_or[gnum_initial_or], contains_ginitial_or_length[index]+50);
  // ginitial_or_length[gnum_initial_or] = contains_ginitial_or_length[index];
  for(i=0;i<ginitial_or_length_old[index];i++){
    if(contains_ginitial_or[index][i]==1){
      /*添加进or中 没有被添加进F，就可以加入or
        */
        ginitial_or[gnum_initial_or][ginitial_or_length[gnum_initial_or]++]=ginitial_or_old[index][i];
      /*添加进初始状态的U中，判断这个U是否已经添加(可能在F中,也可能在U中)*/
      if(isadd2Ufact[ginitial_or_old[index][i]]==0&&isadd2Ffact[ginitial_or_old[index][i]]==0){
        ginitial_state.U[ginitial_state.num_U++]=ginitial_or_old[index][i];
        isadd2Ufact[ginitial_or_old[index][i]]=1;
      }
    }
  }
  gnum_initial_or++;
}

/*ce为提取出来的单个反例*/
void addCounter(int *ce,int celen){
  int i,j,k;
  initGinitiaState();
  /*对ginitial_fact进行插入单个反例对应的F和UF
    更新contains的实现反例集的增加
  */
  
  for(i=0;i<ginitial_state_old.num_F;i++){
    if((ce[ginitial_state_old.F[i]]==1)&&(contains_ginitial_state.F[i]==0)){
      contains_ginitial_state.F[i]=1;
      contains_ginitial_state.num_F++;
    }
  }
  for(i=0;i<ginitial_state_old.num_U;i++){
    if((ce[ginitial_state_old.U[i]]==1)&&(contains_ginitial_state.U[i]==0)){
      contains_ginitial_state.U[i]=1;
      contains_ginitial_state.num_U++;
    }
  }
  for(i=0;i<ginitial_state_old.num_unknown_E;i++){
    if((ce[ginitial_state_old.unknown_E[i]]==1)&&(contains_ginitial_state.unknown_E[i]==1)){
      contains_ginitial_state.unknown_E[i]=1;
      contains_ginitial_state.num_unknown_E++;
    }
  }
  /*对or进行插入*/
  for (i = 0; i < gnum_initial_or_old; i++)
  {
    for (j = 0; j < ginitial_or_length_old[i]; j++)
    {
      if(ce[ginitial_or_old[i][j]]==1&&contains_ginitial_or[i][j]==0){
        contains_ginitial_or[i][j]=1;
        contains_ginitial_or_length[i]++;
      }
    }
  }

  /*更新初始集合*/
  /*首先对初始状态的确定F更新*/
  for(i=0;i<ginitial_state_old.num_F;i++){
    if(contains_ginitial_state.F[i]==1){
      ginitial_state.F[ginitial_state.num_F++] = ginitial_state_old.F[i];
      isadd2Ffact[ginitial_state_old.F[i]]=1;
    }
  }
  /*对于U中存在的情况特殊处理*/
  for(i=0;i<ginitial_state_old.num_U;i++){
    /*如果在U中已经添加，可能是or中的也可能是由unknown形成的*/
    if(contains_ginitial_state.U[i]==1){
      /*是not-a*/
      if(neg_fact[ginitial_state_old.U[i]]!=0){
         /*如果U没有a,说明它只有一个真值是确定的加入到F,有a说明是不确定的，加入到U*/
         /*找到U是否有a，有a的话说明他是非确定的，要添加到U中*/
         int fact_index = ginitial_equivalence_A[neg_fact[ginitial_state_old.U[i]]-1],flag=0;
         for(j=0;j<ginitial_state_old.num_U;j++){
            if(contains_ginitial_state.U[j]==1&&(ginitial_state_old.U[j]==fact_index))
              flag=1;
         }
         /*如果有a,入U*/
         if(flag){
            ginitial_state.U[ginitial_state.num_U++] = ginitial_state_old.U[i];
            isadd2Ufact[ginitial_state_old.U[i]]=1;
         }
         /*没有a,入F*/
         else{
            ginitial_state.F[ginitial_state.num_F++] = ginitial_state_old.U[i];
            isadd2Ffact[ginitial_state_old.U[i]]=1;
         }
      }
      /*是a*/
      else if(neg_true_fact[ginitial_state_old.U[i]]!=0){
         /*如果U没有not-a,加入到F,有not-a加入到U*/
         int fact_index = ginitial_equivalence_notA[neg_true_fact[ginitial_state_old.U[i]]-1],flag=0;
         for(j=0;j<ginitial_state_old.num_U;j++){
            if(contains_ginitial_state.U[j]==1&&(ginitial_state_old.U[j]==fact_index))
              flag=1;
         }
         /*如果有not-a,入U*/
         if(flag){
            ginitial_state.U[ginitial_state.num_U++] = ginitial_state_old.U[i];
            isadd2Ufact[ginitial_state_old.U[i]]=1;
         }
         /*没有not-a,入F*/
         else{
            ginitial_state.F[ginitial_state.num_F++] = ginitial_state_old.U[i];
            isadd2Ffact[ginitial_state_old.U[i]]=1;
         }
      }else{
        ginitial_state.U[ginitial_state.num_U++] = ginitial_state_old.U[i];
        isadd2Ufact[ginitial_state_old.F[i]]=1;
      }
      
    }
  }
  for(i=0;i<ginitial_state_old.num_unknown_E;i++){
    if(contains_ginitial_state.unknown_E[i]==1){
      ginitial_state.unknown_E[ginitial_state.num_unknown_E++] = ginitial_state_old.unknown_E[i];
    }
  }

  /*对or进行更新，同时更新对应的初始状态集*/
  for (i = 0; i < gnum_initial_or_old; i++)
  {
    for (j = 0; j < ginitial_or_length_old[i]; j++)
    {
      /*如果这个oneof或在or的长度为1，那么这个fact就是F里面的*/
      if(contains_ginitial_or_length[i]==1&&contains_ginitial_or[i][j]==1){
        /*判断这个F是否已经添加*/
        if(isadd2Ffact[ginitial_or_old[i][j]]==0){
          ginitial_state.F[ginitial_state.num_F++]=ginitial_or_old[i][j];
          isadd2Ffact[ginitial_or_old[i][j]]=1;
        }
        break;
      }else if(contains_ginitial_or_length[i]>1){
        int flag=0,unum=0;
        for(k=0;k<ginitial_or_length_old[i];k++){
          if(contains_ginitial_or[i][k]==1&&isadd2Ufact[ginitial_or_old[i][k]]==1){
            flag=1;
            unum++;
          }
        }
        if(flag==1&&unum>1)
          addNewOr(i);
        break;
      }
    }
  }
}

/*
  (一)、将初始状态中的谓语加上时间步0加入变量集
  (二)、根据plan对目标状态所有的谓语进行回溯，过程中每步的表示都要按照步数进行标注，得到每步对应的谓语的smt表示
    1.对当前的所有谓语进行，添加-timestep ——> preference
    2.根据状态前的动作，对当前状态进行回溯，（= 当前目标状态~第一次动作后的状态的谓语 【c isvalid true】【c isunsatisfied false】【c-timestep) ——> simulation
    3.回归中动作不为空的前置条件的所有谓语添加-timestep ——> preference
  (三)、生成初始状态assert
  (四)、对非第0步的所有具有neg的谓语进行处理（not），第0步具有neg属性的在第(一)、(二)中完成
  (五)、将所有变量转换为smt变量
  (六)、进行sat验证，如果有反例，将反例保存到一个int数组中，并返回true\false
  注意：谓语的最大上限为10000，超出会报错（所有需要的初始化均为10000，如有需要可调整）
*/
Bool conputerCounter(int *ce,int *celen)
{
  /*每次迭代，neg的哈希表要重置
    当前只使用了fact_unuse_zero，当-0的谓语进行添加时，要进行约束，不能对不存在的添加
    非-0的谓语，要进行约束，可以添加
    */
  memset(fact_unuse_zero,0,10000);
  memset(fact_step,0,10000);
  if(neg_assert==NULL){
    neg_assert = (char*)calloc(10,sizeof(char));
  }else{
    memset(neg_assert,0,strlen(neg_assert));
    realloc(neg_assert, 10);
  }
  
  int i, j;
  Bool success = FALSE;
  PredicateString *predicate_string;
  /*存储当前目标状态根据plan回溯到初始状态的smt公式*/
  char *simulation = (char *)calloc(1, sizeof("(assert (and true "));
  strcat(simulation,"(assert (and true ");
  /*（否定）存储目标状态和plan中动作的前置条件*/
  char *preference = (char *)calloc(1, sizeof("(not (and "));
  strcat(preference,"(not (and ");
  /*set结构变量表，存储运行中的所有变量*/
  SimpleSet variables;
  set_init(&variables);
  /*(一)*/
  /*初始状中的谓语，以步数0结尾，加入到变量表中*/
  for (i = 0; i < ginitial_state_old.num_F; i++)
  {
    set_add(&variables,toSmtVariableString(Fact2SmtString(ginitial_state_old.F[i]),0));
    /*对第0步的neg针对处理*/
    if(neg_fact[ginitial_state_old.F[i]]!=0){
      assert_Neg(ginitial_state_old.F[i],0,&variables);
    }
  }
  for (i = 0; i < ginitial_state_old.num_U; i++)
  {
    set_add(&variables,toSmtVariableString(Fact2SmtString(ginitial_state_old.U[i]),0));
    /*对第0步的neg针对处理*/
    /*print_ft_name(ginitial_state.U[i]);
    printf(" %d\n",ginitial_state.U[i]);*/
    if(neg_fact[ginitial_state_old.U[i]]!=0){
      assert_Neg(ginitial_state_old.U[i],0,&variables);
    }
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

  /*(二)*/
  int timestep = gnum_plan_ops;
  /*current_goal_fact存储当前的目标状态谓语*/ 
  int goal_len=ggoal_state.num_F+ggoal_state.num_U;
  int *current_goal_fact=(int *)calloc(10000, sizeof(int));
  /*目标状态加入preference*/
  for(i=0;i<ggoal_state.num_F;i++){
    current_goal_fact[i]=ggoal_state.F[i];
    preference=contactString(preference,toSmtVariableString(Fact2SmtString(ggoal_state.F[i]),timestep));
    set_add(&variables,toSmtVariableString(Fact2SmtString(ggoal_state.F[i]),timestep));
  }
  for(i=0;i<ggoal_state.num_U;i++){
    current_goal_fact[ggoal_state.num_F+i]=ggoal_state.U[i];
    preference=contactString(preference,toSmtVariableString(Fact2SmtString(ggoal_state.U[i]),timestep));
    set_add(&variables,toSmtVariableString(Fact2SmtString(ggoal_state.U[i]),timestep));
  }
  
  /*对目标状态进行回归，得到回归assert*/
  int new_goal[10005]={0};
  for (i = timestep-1; i >=0; i--)
  {
    /*
    printf("\n%d :",i);
    print_op_name( gplan_ops[i] );
    */
  //  print_op_name( gplan_ops[i] );
    Action *a = gop_conn[gplan_ops[i]].action;
    int new_len=0;
    for(j=0;j<goal_len;j++){        
        addAction2Goal(&simulation,&preference,current_goal_fact[j],a,&new_len,&variables,new_goal,i+1);
    }
    /*对当前需要回归的fact进行记录*/
    memset(current_goal_fact,0,10000);
    updNewgoal(new_goal,current_goal_fact,&new_len);
    /*重置需要添加的fact为空*/
    memset(new_goal,0,10000);
    goal_len = new_len;
  }
  preference = contactString(preference,") )");
  simulation = contactString(simulation,preference);
  simulation = contactString(simulation,") )\n");
  free(current_goal_fact);
  /*printf("\nsmt: %s\n",simulation);*/

  /*(三)*/
  /*对初始状态进行转换*/
  char *init_smt = (char*)calloc(1,sizeof("(assert (AND"));
  strcat(init_smt,"(assert (AND");
  
  /*对存在于or中的fact在set中记录，不重复添加*/
  int factset[10000]={0};
  for (i = 0; i < gnum_initial_or_old; i++)
  {
    for (j = 0; j < ginitial_or_length_old[i]; j++)
    {
      factset[ginitial_or_old[i][j]]=1;
    }
  }
  /*printf("/n输出初始状态");
  print_state(ginitial_state);*/
  
  /*先将fact中非or部分加入*/
  for(i=0;i<ginitial_state_old.num_F;i++){
      if(factset[ginitial_state_old.F[i]]!=1){
          char *tmp = toSmtVariableString(Fact2SmtString(ginitial_state_old.F[i]),0);
          init_smt=contactString(init_smt, tmp);    
          init_smt=contactString(init_smt, "\n");
          if(set_add(&variables, tmp)){
            free(tmp);
          }
      }
  }
  /*如果是U里面的,是not有neg的,并且没有在or中,就要添加一个约束,只能存在一个*/
  for(i=0;i<ginitial_state_old.num_U;i++){
      /*对于这种情况,不在or中的not
        要对其进行约束,因为在SMT中not-a和a不能在没有or约束下共存于and中
        所以除了添加进入or中,还要对not-a进行处理
        */
      // if(factset[ginitial_state_old.U[i]]!=1){
      //     char *tmp = toSmtVariableString(Fact2SmtString(ginitial_state_old.U[i]),0);
      //     init_smt=contactString(init_smt, tmp);    
      //     init_smt=contactString(init_smt, "\n");  
      //     if(set_add(&variables, tmp)){
      //       free(tmp);
      //     }
      // }

      /*对U中的not-a进行处理,三种情况:1.oneof(不需要处理) 2.or(对not进行添加) 3.unknown(除了对not进行添加,还要对a进行屏蔽)
        所以只需要判断这个not是否在or中,其它的不用处理（必然处理过的情况，如果有not-a在U中，必然有a在U中，这个不需要处理，因为已经在处理a时处理了---cff）
        用oneof对not-a和a进行约束
      */

      /*存在not-a 但是不在oneof中，这种单独生成一个oneof*/
      if(neg_fact[ginitial_state_old.U[i]]!=0&&factset[ginitial_state_old.U[i]]!=1){
          char *neg_a = toSmtVariableString(Fact2SmtString(ginitial_state_old.U[i]),0);
          int index = neg_fact[ginitial_state_old.U[i]]-1;
          char *a = toSmtVariableString(Fact2SmtString(ginitial_equivalence_A[index]),0);
          char *tmp = (char*)calloc(1,sizeof("(or "));
          strcat(tmp,"(or");
          tmp = contactString(tmp,neg_a);
          tmp = contactString(tmp,a);
          tmp = contactString(tmp,")\n");
          tmp = contactString(tmp,"(or (not");
          tmp = contactString(tmp,neg_a);
          tmp = contactString(tmp,")");
          tmp = contactString(tmp,"(not");
          tmp = contactString(tmp,a);
          tmp = contactString(tmp,"))\n");
          init_smt=contactString(init_smt, tmp);
          // init_smt=contactString(init_smt, n);    
          // init_smt=contactString(init_smt, "\n");  
          if(set_add(&variables, neg_a)){
            free(neg_a);
          }
          if(set_add(&variables, a)){
            free(a);
          }
        free(tmp);
      }
  } 

  /*再将所有的or添加进来*/
  for (i = 0; i < gnum_initial_or_old; i++)
  {
    char *or_smt = (char*)calloc(1,sizeof("(OR"));
    strcat(or_smt,"(OR");
    for (j = 0; j < ginitial_or_length_old[i]; j++)
    {
      char *tmp = toSmtVariableString(Fact2SmtString(ginitial_or_old[i][j]),0);
      or_smt=contactString(or_smt, tmp);
      if(set_add(&variables, tmp)){
        free(tmp);
      }
    }
    or_smt=contactString(or_smt, ")"); 
    init_smt=contactString(init_smt, or_smt);    
    init_smt=contactString(init_smt, "\n");
    free(or_smt);  
  }
  init_smt=contactString(init_smt, ") )");
  /*printf("\n%s\n",init_smt);*/

  /*(四)*/
  /*对所有的neg_fact集合进行处理，非第0步*/
  for (i = 0; i < gnum_initial_equivalence; i++)
  {
    /*包括可能出现的所有的步数*/
    for(j=1;j<=timestep;j++){
      /*对于neg_i在第j步*/
      assert_Neg(ginitial_equivalence_notA[i],j,&variables);
    }
    /*初始化等价set*/
  }

  /*(五)*/
  /*将所有的变量加入，并且构造最终的smt*/
  char *final_smt=(char*)calloc(10,sizeof(char));
  uint64_t var_length=set_length(&variables);
  char** var_string = set_to_array(&variables,&var_length);
  
  printf("\nvar_size: %d\n",var_length);
  // printf("\n");
  
  for(i=0;i<var_length;i++){
    char *var = (char*)calloc(1,sizeof("(declare-fun"));
    strcat(var,"(declare-fun");
    var = contactString(var,var_string[i]);
    var = contactString(var,"() Bool)\n");
    final_smt = contactString(final_smt,var);
    free(var);
    free(var_string[i]);
  }
  final_smt=contactString(final_smt,simulation);

  final_smt=contactString(final_smt,neg_assert);

  final_smt=contactString(final_smt,init_smt);
  toLower(final_smt);
  set_destroy(&variables);
  printf("\n%s\n",init_smt);
  /*printf("\n%s\n",preference);*/
  // printf("\n%s\n",final_smt);
  /*printf("\n%s\n",neg_assert);*/
  free(simulation);
  free(preference);
  free(init_smt);
  /*(六)*/

  Z3_config cfg;
  Z3_context ctx;
  Z3_solver s;
  cfg = Z3_mk_config();
  Z3_set_param_value(cfg, "model", "true");
  ctx = Z3_mk_context(cfg);
  Z3_set_error_handler(ctx, error_handler);
  Z3_del_config(cfg);
  s= mk_solver(ctx);

  Z3_ast_vector f = Z3_parse_smtlib2_string(ctx,
                               /* the following string has a parsing error: missing parenthesis */
                              final_smt,
                               0, 0, 0,
                               0, 0, 0);
  // printf("formula: %s\n", Z3_ast_vector_to_string(ctx, f));
  /*加入所有的断言*/
  int n = Z3_ast_vector_size(ctx,f);
  printf("\n当前收集的断言数：%d\n",n);
  for(i=0;i<n;i++)
    Z3_solver_assert(ctx, s, Z3_ast_vector_get(ctx,f,i));

  /*提取反例*/
  Z3_model m      = 0;
  Z3_lbool result = Z3_solver_check(ctx, s);
  char *counter ;
  printf("\n%d\n",result);
  switch (result) {
    /*未找到反例*/
    case Z3_L_FALSE:
        printf("unsat\n");
        Z3_solver_dec_ref(ctx, s);
        Z3_del_context(ctx);
        free(final_smt);
        return false;
    case Z3_L_UNDEF:
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        /*printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));*/
        /*这里只是可能的，不一定有解*/
        // char *counter = Z3_model_to_string(ctx, m);
        *celen = extractCounter(ctx,m,ce);
        break;
    /*找到反例*/
    case Z3_L_TRUE:
        m = Z3_solver_get_model(ctx, s);
        if (m) Z3_model_inc_ref(ctx, m);
        // char *counter = Z3_model_to_string(ctx, m);
        // /*printf("\n%s\n",counter);*/
        *celen = extractCounter(ctx,m,ce);
        break;
  }
  Z3_solver_dec_ref(ctx, s);
  Z3_del_context(ctx);
  free(final_smt);
  return true; 
}



  /*
  for (i = 0; i < gnum_initial_or; i++)
  {
    printf("\nOR: ");
    for (j = 0; j < ginitial_or_length[i]; j++)
    {
      print_ft_name(ginitial_or[i][j]);
      printf(" ");
    }
  }
  */
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