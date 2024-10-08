

/*
 * THIS SOURCE CODE IS SUPPLIED  ``AS IS'' WITHOUT WARRANTY OF ANY KIND, 
 * AND ITS AUTHOR AND THE JOURNAL OF ARTIFICIAL INTELLIGENCE RESEARCH 
 * (JAIR) AND JAIR'S PUBLISHERS AND DISTRIBUTORS, DISCLAIM ANY AND ALL 
 * WARRANTIES, INCLUDING BUT NOT LIMITED TO ANY IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
 * ANY WARRANTIES OR NON INFRINGEMENT.  THE USER ASSUMES ALL LIABILITY AND
 * RESPONSIBILITY FOR USE OF THIS SOURCE CODE, AND NEITHER THE AUTHOR NOR
 * JAIR, NOR JAIR'S PUBLISHERS AND DISTRIBUTORS, WILL BE LIABLE FOR 
 * DAMAGES OF ANY KIND RESULTING FROM ITS USE.  Without limiting the 
 * generality of the foregoing, neither the author, nor JAIR, nor JAIR's
 * publishers and distributors, warrant that the Source Code will be 
 * error-free, will operate without interruption, or will meet the needs 
 * of the user.
 */







/*********************************************************************
 * File: main.c
 * Description: The main routine for the FastForward Planner.
 *              Conformant version in collaboration with Ronen Brafman.
 *
 * Author: Joerg Hoffmann 2002
 * 
 *********************************************************************/ 







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








/*
 *  ----------------------------- GLOBAL VARIABLES ----------------------------
 */




/**
 * @brief 
 * 这还是一个测试
 * 测试git上传忽略功能
 * 
 */







/*******************
 * GENERAL HELPERS *
 *******************/







struct tms start, end;

/* runtime statistics etc.
 */
float gtempl_time = 0, greach_time = 0, grelev_time = 0, gconn_time = 0, gmem_time = 0;
float gsearch_time = 0, geval_time = 0, gcnf_time = 0, genc_time = 0, gsat_time = 0;
float grs_time = 0, grs_sat_time = 0, gss_time = 0, gsc_time = 0;
float gr_sat_time = 0, grp_sat_time = 0, gr_cnf_time = 0, gr_enc_time = 0, gmembership_time = 0;
float gcounter_time=0;
int gsat_calls = 0, gcnfs = 0, grs_sat_calls = 0, gss_sat_calls = 0, gsc_sat_calls = 0;
int gr_sat_calls = 0, grp_sat_calls = 0;
int grs_comps = 0, grs_conf_comps = 0;
int grs_hits = 0, gss_hits = 0, gdp_calls = 0, gup_calls = 0;



int sample_time;


/* the command line inputs
 */
struct _command_line gcmd_line;

/* number of states that got heuristically evaluated
 */
int gevaluated_states = 0;

/* maximal depth of breadth first search
 */
int gmax_search_depth = 0;



/* CNF statistic
 */
float *gsum_k_clauses, gsum_clauses = 0;








/***********
 * PARSING *
 ***********/







/* used for pddl parsing, flex only allows global variables
 */
int gbracket_count;
char *gproblem_name;

/* The current input line number
 */
int lineno = 1;

/* The current input filename
 */
char *gact_filename;

/* The pddl domain name
 */
char *gdomain_name = NULL;

/* loaded, uninstantiated operators
 */
PlOperator *gloaded_ops = NULL;

/* stores initials as fact_list 
 */
PlNode *gorig_initial_facts = NULL;

/* stores initial ors as an array of OR lists
 */
PlNode_pointer *gorig_initial_ors;
int gnum_orig_initial_ors;

/* stores initial oneofs as an array of ONEOF lists
 */
PlNode_pointer *gorig_initial_oneofs;
int gnum_orig_initial_oneofs;

/* not yet preprocessed goal facts
 */
PlNode *gorig_goal_facts = NULL;

/* axioms as in UCPOP before being changed to ops
 */
PlOperator *gloaded_axioms = NULL;

/* the types, as defined in the domain file
 */
TypedList *gparse_types = NULL;

/* the constants, as defined in domain file
 */
TypedList *gparse_constants = NULL;

/* the predicates and their arg types, as defined in the domain file
 */
TypedListList *gparse_predicates = NULL;

/* the objects, declared in the problem file
 */
TypedList *gparse_objects = NULL;


/* connection to instantiation ( except ops, goal, initial )
 */

/* all typed objects 
 */
FactList *gorig_constant_list = NULL;

/* the predicates and their types
 */
FactList *gpredicates_and_types = NULL;












/*****************
 * INSTANTIATING *
 *****************/









/* global arrays of constant names,
 *               type names (with their constants),
 *               predicate names,
 *               predicate aritys,
 *               defined types of predicate args
 */

Token gconstants[MAX_CONSTANTS];
int gnum_constants = 0;
Token gtype_names[MAX_TYPES];
int gtype_consts[MAX_TYPES][MAX_TYPE];
Bool gis_member[MAX_CONSTANTS][MAX_TYPES];
int gtype_size[MAX_TYPES];
int gnum_types = 0;
Token gpredicates[MAX_PREDICATES];
int garity[MAX_PREDICATES];
int gpredicates_args_type[MAX_PREDICATES][MAX_ARITY];
int gnum_predicates = 0;





/* the domain in integer (Fact) representation
   初始状态的表示，初始为真、初始未知的，初始是or的，初始三oneof的
 */
Operator_pointer goperators[MAX_OPERATORS];
int gnum_operators = 0;
Fact *gfull_initial;
int gnum_full_initial = 0;
Fact *gfull_unknown_initial;
int gnum_full_unknown_initial;
WffNode_pointer *gfull_or_initial;
int gnum_full_or_initial;
WffNode_pointer *gfull_oneof_initial;
int gnum_full_oneof_initial;
WffNode *ggoal = NULL;




/* stores inertia - information: is any occurence of the predicate
 * added / deleted in the uninstantiated ops?
 * is any occurence of the predicate unknown?
 * 在未实例化的操作中是否出现添加/删除谓词?谓词的出现是否未知?
 */
Bool gis_added[MAX_PREDICATES];
Bool gis_deleted[MAX_PREDICATES];
Bool gis_unknown[MAX_PREDICATES];



/* splitted initial state:
 * initial non static facts,
 * initial static facts, divided into predicates
 * (will be two dimensional array, allocated directly before need)
 *
 * the same mirrored for unknown facts -- "known negatives" is transferred
 * here to "known positives and unknowns"; seems more adequate for later 
 * purposes, giving access to unknowns directly.
 * 存储数据，但是用的应该是下面规划图里面的
 */
Facts *ginitial = NULL;
int gnum_initial = 0;
Facts *gunknown_initial = NULL;
int gnum_unknown_initial = 0;
Fact **ginitial_predicate;
int *gnum_initial_predicate;
Fact **gunknown_initial_predicate;
int *gnum_unknown_initial_predicate;
/* this here stores dependencies between initial variables:
 * when translating negations of an unkwown literal we need
 * to remember that the translation, while unkown, will
 * always have the respective inverse value.
 */
Facts *ginitial_ft_equivalence_A;
Facts *ginitial_ft_equivalence_notA;
int gnum_initial_ft_equivalence = 0;



/* the type numbers corresponding to any unary inertia
 */
int gtype_to_predicate[MAX_PREDICATES];
int gpredicate_to_type[MAX_TYPES];

/* (ordered) numbers of types that new type is intersection of
 */
TypeArray gintersected_types[MAX_TYPES];
int gnum_intersected_types[MAX_TYPES];



/* stores which predicate is a translation of which other one.
 */
int gtranslated_predicate_to[MAX_PREDICATES];



/* splitted domain: hard n easy ops
 */
Operator_pointer *ghard_operators;
int gnum_hard_operators;
NormOperator_pointer *geasy_operators;
int gnum_easy_operators;



/* so called Templates for easy ops: possible inertia constrained
 * instantiation constants
 */
EasyTemplate *geasy_templates;
int gnum_easy_templates;



/* first step for hard ops: create mixed operators, with conjunctive
 * precondition and arbitrary effects
 */
MixedOperator *ghard_mixed_operators;
int gnum_hard_mixed_operators;



/* hard ''templates'' : pseudo actions
 */
PseudoAction_pointer *ghard_templates;
int gnum_hard_templates;



/* store the final "relevant facts"
   规划连接最终查找的fact
 */
Fact grelevant_facts[MAX_RELEVANT_FACTS];
int gnum_relevant_facts = 0;
int gnum_pp_facts = 0;

/* the final actions and problem representation
 */
Action *gactions;
int gnum_actions;

State ggoal_state;
/* initially valid implications
 */
int *ginitial_equivalence_A;
int *ginitial_equivalence_notA;
int gnum_initial_equivalence;
/* to know how much space we need for unknown conds in states
 */
int gmax_E;

/* 下面的初始状态和初始or当作反例
  */
State ginitial_state;
/* the initial OR constraints in final coding
 */
int **ginitial_or;
int *ginitial_or_length;
int gnum_initial_or;


/* 存储反例子相关数据
 */

/*副本*/
State ginitial_state_old;
int **ginitial_or_old;
int *ginitial_or_length_old;
int gnum_initial_or_old;
/*存储的是当前的反例集，用于判断是否在初始反例集中*/
State contains_ginitial_state;
int **contains_ginitial_or;
int *contains_ginitial_or_length;
int contains_gnum_initial_or;
/*判断是否是U中的，或者是否是or中的*/
Bool isadd2Ufact[10000]={0};
Bool inOrfact[10000]={0};
Bool isadd2Ffact[10000]={0};
/**********************
 * CONNECTIVITY GRAPH *
 **********************/







/* one ops (actions) array ...
 */
OpConn *gop_conn;
int gnum_op_conn;

/* one effects array ...
 */
EfConn *gef_conn;
int gnum_ef_conn;

/* one facts array.
 */
FtConn *gft_conn;
int gnum_ft_conn;



/* max #conds. for max clauses computation.
 */
int gmax_C;



/* max U: all initial Us plus facts that are 
 * added / deleted by a conditional effect with poss_U conds.
 * (important for various memory allocations)
 */
int gmax_U;
int gmax_CNFU;

/* we get these max #s of clauses and lits.
 */
int gmax_clauses;
int gmax_rs_clauses;
int gmax_literals;









/*******************
 * SEARCHING NEEDS *
 *******************/







/* byproduct of fixpoint: applicable actions
 */
int *gA;
int gnum_A = 0;



/* communication from extract 1.P. to search engines:
 * 1P action choice
 */
int *gH;
int gnum_H = 0;



/* always stores (current) serial plan
 */
int gplan_ops[MAX_PLAN_LENGTH];
int gnum_plan_ops = 0;



/* stores the states that the current plan goes through
 */
State gplan_states[MAX_PLAN_LENGTH + 1];



/* the clauses to be communicated to the SAT solver for
 * determining inferred literals.
 */
TimedLiteral **gclauses;
int *gclause_length;
int gnum_fixed_clauses;/* up to end of gplan */
int gnum_clauses;/* beyond that, ie dynamic search fraction */ 
int gfixed_endtime = 0;

/* array; maps ft / time pair to its number in CNF encoding.
 */
int **gcodes;
int gnum_fixed_c;


/* inverse mapping, to undo changes in table.
 */
int *gcf, *gct, gnum_c;



/* statistics: count nr. of times the "disjunction minimisation" actually
 * minimised something
 */
int gremoved_lits = 0;



/* stores the current DP decisions including unit propagations.
 *
 * is for DP given in state_transitions.c!!!!!
 *
 * have to make this global as it's also accessed from repeated states --
 * when checking stagnation. I know it's ugly...
 */
int *gdecision_stack;
int gnum_decision_stack;



/* for each possible ft code, a pointer to connected dynamic list
 * of member elements, ie the clauses in which it participates,
 * positive and negative.
 *
 * used in state_transitions DP solver. global as accessed from search.c
 * in reset between ehc and bfs switch.
 */
MemberList_pointer *gpos_c_in_clause_start;
MemberList_pointer *gpos_c_in_clause_fixed;/* before here, list corresp. to fixed CNF */
MemberList_pointer *gpos_c_in_clause_end;/* before here, members of current list */
MemberList_pointer *gneg_c_in_clause_start;
MemberList_pointer *gneg_c_in_clause_fixed;
MemberList_pointer *gneg_c_in_clause_end;



/* automatically checked Bool saying if sufficient criteria for
 * "more facts are always better" holds.
 */
Bool gdomination_valid;


/*存储有等价fact的fact*/
int neg_fact[10000]={0};
int neg_true_fact[10000]={0};
/*用于对neg_fact的添加的去重*/
Bool fact_unuse_zero[10000]={0};
Bool fact_step[10000]={0};
/*存储初始就在or中的*/
int factset[10000]={0};





/*
 *  ----------------------------- HEADERS FOR PARSING ----------------------------
 * ( fns defined in the scan-* files )
 */







void get_fct_file_name( char *filename );
void load_ops_file( char *filename );
void load_fct_file( char *filename );


void freesomeVar(){
  int i,j;
  for ( i = 0; i < MAX_PLAN_LENGTH + 1; i++ ) {
    /*gnum_ft_conn 最终fact的数量*/
    if(gnum_ft_conn>0)
      free(gplan_states[i].F);
    free(gplan_states[i].U);
    free(gplan_states[i].unknown_E);
  }
  /*initialize_state_transitions();*/
  for (i = 0; i < gmax_clauses; i++)
  {
    free(gclauses[i]);
    // gclauses[i] = (TimedLiteral *)calloc(gmax_literals, sizeof(TimedLiteral));
    // gclause_length[i] = 0;
  }
  free(gclauses);
  free(gclause_length);

  for (i = 0; i < MAX_PLAN_LENGTH + 1; i++)
  {
    free(gcodes[i]);
    // gcodes[i] = (int *)calloc(gnum_ft_conn, sizeof(int));
  }
  free(gcodes);

  free(gcf);
  free(gct);

  free(gpos_c_in_clause_start);
  free(gpos_c_in_clause_fixed);
  free(gpos_c_in_clause_end);
  free(gneg_c_in_clause_start);
  free(gneg_c_in_clause_fixed);
  free(gneg_c_in_clause_end);
  free(lhitting_set);
  free(gdecision_stack);
  free(lassigned);
  free(gsum_k_clauses);
  /*extend_fixed_clauses_base( 0, 0 ); 不会重复赋值*/
  /*extend_fixed_clauses_base_encoding( 0 ); 无*/
  /*initialize_relax();*/
  if(gnum_ft_conn>0)
    free(lcurrent_goals.F);
  free(lcurrent_goals.U);
  free(lcurrent_goals.unknown_E);
  free(gH);
  free(gA);
  free(lnum_U);
  for (i = 0; i < RELAXED_STEPS + MAX_PLAN_LENGTH; i++)
  {
    free(lU[i]);
  }
  free(lU);
  free(lF);
  free(lE);
  free(lch_E);
  free(l0P_E);
  free(l0P_O);
  free(lch_O);
  if (gcmd_line.heuristic == 0 ||
      gcmd_line.heuristic == 1)
  {
    int maxcl = gnum_ft_conn ;
    // free(lr_clause_length);
    for (i = 0; i < maxcl; i++)
    {
      free(lr_clauses[i]);
    }
    free(lr_clauses);

    free(lr_codes);
    free(lr_cf);
    free(lr_assigned);
    free(lr_decision_stack );

    free(lr_pos_c_in_clause_start);
    free(lr_pos_c_in_clause_end);
    free(lr_neg_c_in_clause_start);
    free(lr_neg_c_in_clause_end);
  } /* if heuristic == 1 */

  if ( gcmd_line.dominating ) {
    free(lrs_clause_length[0]);
    free(lrs_clause_length[1]);
    free(lrs_clause_length);
    free(lrs_dp_clause_length); 
    for ( i = 0; i < gmax_rs_clauses; i++ ) {
      free(lrs_clauses[0][i]); 
      free(lrs_clauses[1][i]); 
      free(lrs_dp_clauses[i]); 
    }
    free(lrs_clauses[1]);
    free(lrs_clauses[0]);
    free(lrs_clauses);

    free(lrs_dp_clauses);
    for ( i = 0; i <= MAX_PLAN_LENGTH; i++ ) {
      free(lrs_codes[0][i]); 
      free(lrs_codes[1][i]); 
    }
    free(lrs_codes[0]);
    free(lrs_codes[1]);
    free(lrs_codes);
    
    free(lrs_cn);
    free(lrs_cf);
    free(lrs_ct);
    
    free(lrs_hitting_set);
    free(lrs_assigned);
    free(lrs_decision_stack);

    free(lrs_pos_c_in_clause_start);
    free(lrs_pos_c_in_clause_end);
    free(lrs_neg_c_in_clause_start);
    free(lrs_neg_c_in_clause_end);
  }
}


void initSomeVar(){
  int i,j;
  times( &start );
  /* 2 * #initial equivalences plus #initial OR clauses plus
   * max ops to induce * (max ef implic of op<最大效果隐含数> * max noop implic) plus
   * max #additional clauses for conflict check plus
   * max #additional clauses for infer clauses
   */
  /*计算会有的clause最大数量*/
  gmax_clauses = 
    (2 * gnum_initial_equivalence) +
    (MAX_PLAN_LENGTH * (gmax_E + (2 * gmax_CNFU))) +
    gmax_C * 2 +
    1;
  for ( i = 0; i < gnum_initial_or; i++ ) {
    /* all ordered pairs of fts yield one binary clause.
      对于所有的有序配对的fts（符号翻译集合），会产生一个二元子句
     */
    gmax_clauses += ginitial_or_length[i] * (ginitial_or_length[i] - 1);
  }
  /*printf("gmax_clauses:%d\n",gmax_clauses);*/
  /* 2 * #initial equivalences plus #initial OR clauses plus
   * 2 * [as we got two cnfs glued together] max ops to induce * 
   * (max ef implic of op * max noop implic) plus
   * max #additional clauses for improvement clauses
   */
  gmax_rs_clauses = 
    (2 * gnum_initial_equivalence) +
    (2 * MAX_PLAN_LENGTH * (gmax_E + (2 * gmax_CNFU))) +
    2;
  for ( i = 0; i < gnum_initial_or; i++ ) {
    /* all ordered pairs of fts yield one binary clause.
      这些也会产生子句
     */
    gmax_rs_clauses += ginitial_or_length[i] * (ginitial_or_length[i] - 1);
  }

  /* max. size effect axiom
   */ 
  gmax_literals = gmax_C + 1;
  /* if all effs of maxE op contradict with the same fact then
   * the resulting noop clause is this long.
   */ 
  if ( gmax_E + 2 > gmax_literals ) {
    gmax_literals = gmax_E + 2;
  }
  /* ini OR lengths...
   */
  for ( i = 0; i < gnum_initial_or; i++ ) {
    if ( ginitial_or_length[i] > gmax_literals ) {
      gmax_literals = ginitial_or_length[i];
    }
  }

  /* make space in plan states info, and relax; don't count the time for that.
     这个地方的没有free
   */
  for ( i = 0; i < MAX_PLAN_LENGTH + 1; i++ ) {
    /*gnum_ft_conn 最终fact的数量*/
    make_state( &(gplan_states[i]), gnum_ft_conn );
  }
  /*为规划算法中使用的各种全局数组分配内存*/
  initialize_state_transitions();
  /*生成规划算法中使用的子句，以便在后续的规划过程中使用*/
  extend_fixed_clauses_base( 0, 0 );
  /*为每个子句中的文字（literal）分配一个唯一的编码，以便在后续的推理过程中使用*/
  extend_fixed_clauses_base_encoding( 0 );
  /*简化或放宽问题的约束条件，以便更容易地解决问题*/
  /*用于创建各种数据结构和初始化变量，以便后续的规划算法可以进行有效的推理和搜索*/
  initialize_relax();
  if ( gcmd_line.dominating ) {
    initialize_repeated_states();
  }
  source_to_dest( &(gplan_states[0]), &ginitial_state );

  times( &end );
  TIME( gmem_time );
}

/*
 *  ----------------------------- MAIN ROUTINE ----------------------------
 */

struct tms lstart, lend;

int main( int argc, char *argv[] )

{

  /* resulting name for ops file
   */
  char ops_file[MAX_LENGTH] = "";
  /* same for fct file 
   */
  char fct_file[MAX_LENGTH] = "";
  


  int i;
  Bool found_plan;

  times ( &lstart );

  /*初始化命令行输入的参数*/
  gcmd_line.display_info = 1;
  gcmd_line.debug = 0;
  gcmd_line.ehc = TRUE;
  gcmd_line.help = TRUE;
  gcmd_line.manual = FALSE;
  gcmd_line.heuristic = 1;
  gcmd_line.stagnating = TRUE;
  gcmd_line.dominating = TRUE;
  gcmd_line.breadth_bfs = FALSE;
  gcmd_line.R = FALSE;
  gcmd_line.A = FALSE;
  gcmd_line.T = FALSE;
  gcmd_line.P = FALSE;
  memset(gcmd_line.ops_file_name, 0, MAX_LENGTH);
  memset(gcmd_line.fct_file_name, 0, MAX_LENGTH);
  memset(gcmd_line.path, 0, MAX_LENGTH);
  /*输入*/ 
  /* command line treatment
   */
  if ( argc == 1 || ( argc == 2 && *++argv[0] == '?' ) ) {
    ff_usage();
    exit( 1 );
  }
  if ( !process_command_line( argc, argv ) ) {
    ff_usage();
    exit( 1 );
  }

  /* make file names
   */

  /* one input name missing
   */
  if ( !gcmd_line.ops_file_name || 
       !gcmd_line.fct_file_name ) {
    fprintf(stdout, "\nff: two input files needed\n\n");
    ff_usage();      
    exit( 1 );
  }
  /* add path info, complete file names will be stored in
   * ops_file and fct_file 
   */
  sprintf(ops_file, "%s%s", gcmd_line.path, gcmd_line.ops_file_name);
  sprintf(fct_file, "%s%s", gcmd_line.path, gcmd_line.fct_file_name);

  /* parse the input files
   */

  /* start parse & instantiation timing
   */
  times( &start );
  /* domain file (ops)
   */
  if ( gcmd_line.display_info >= 1 ) {
    printf("\nff: parsing domain file");
  } 
  /* it is important for the pddl language to define the domain before 
   * reading the problem 
   */
  /*加载domain文件*/
  load_ops_file( ops_file );
  /* problem file (facts)
   */  
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\nff: parsing problem file"); 
  } 
  load_fct_file( fct_file );
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\n\n");
  }

  /* This is needed to get all types.
   */
  build_orig_constant_list();
  /*动作描述语言：ADL 允许更灵活的动作描述，包括连续效应、非确定性和部分确定性
  可能是非确定性，当前的版本不能解决这个问题/
  /* last step of parsing: see if it's an ADL domain!
   */
  if ( !make_adl_domain() ) {
    printf("\nff: this is not an ADL problem!");
    printf("\n    can't be handled by this version.\n\n");
    exit( 1 );
  }

  /* now instantiate operators;
   */

  /**************************
   * first do PREPROCESSING * 
   **************************/

  /* start by collecting all strings and thereby encoding 
   * the domain in integers.
   */
  /*将domain中的字符串编辑为数字，用表来映射*/
  /*同时将第一步时候的状态以及动作的条件按照这个数字表保存*/
  /*这一步将常量、谓语、动作存储到表中*/
  
  /*这里还是初始的oneof*/
  encode_domain_in_integers();

  /* inertia preprocessing, first step:
   *   - collect inertia information
   *   - split initial state into
   *        _ arrays for individual predicates
   *        - arrays for all static relations
   *        - array containing non - static relations
   */
  /*
    收集惯性信息（inertia information）。
      将初始状态拆分为：
      用于各个谓词的数组。
      用于所有静态关系的数组。
      包含非静态关系的数组。
  */
  do_inertia_preprocessing_step_1();

  /* normalize all PL1 formulae in domain description:
   * (goal, preconds and effect conditions)
   *   - simplify formula
   *   - expand quantifiers
   *   - NOTs down
   * 对领域描述中所有PL1公式的规范化过程
   *  简化公式：对公式进行简化操作，使其更易处理和理解。
      展开量词：展开公式中的量词，以便更清晰地表达公式的含义。
      将否定符号下推：对公式中的否定符号进行下推，使得公式更易于处理和计算。
    包括将目标（goal）公式直接转换为析取范式（DNF）的过程
    还有将CNF可以转换的转换为true
   */
  normalize_all_wffs();

  /* translate negative preconds: introduce symmetric new predicate
   * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
   负前置条件（negative preconds）转换为对称的新谓词
   */
  translate_negative_preconds();


  /* split domain in easy (disjunction of conjunctive preconds)
   * and hard (non DNF preconds) part, to apply 
   * different instantiation algorithms
   * 分为简单部分（DNF）和非简单部分（CNF），以配备不同的算法，按照什么方式来分
   * 一个动作变为删除和增加一些状态
   */
  split_domain();


  /***********************************************
   * PREPROCESSING FINISHED                      *
   *                                             *
   * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
   ***********************************************/

  build_easy_action_templates();
  build_hard_action_templates();

  times( &end );
  TIME( gtempl_time );
  /*记录执行可行性分析时间 --gtempl_time*/
  times( &start );

  /* perform reachability analysis in terms of relaxed 
   * fixpoint
   以放宽的不动点为基础执行可达性分析
   */
  perform_reachability_analysis();

  times( &end );
  TIME( greach_time );
  /*记录greach_time*/
  times( &start );

  /* collect the relevant facts and build final domain
   * and problem representations.
    收集相关事实，并构建最终的domain和problem表示
    这里的init初始状态是未知的
    而寻找要改成已知的
   */
  
  /*形成最终结果*/
  collect_relevant_facts();


  /*Action *a;
  for(a = gactions;a;a=a->next){
    print_Action(a);
    printf("11111\n");
  }*/
  /*修改inial看看结果
    */
   /*
   print_state(ginitial_state);
   
   ginitial_state.num_U = 4;
   ginitial_state.U[2] = ginitial_state.U[5];
   ginitial_state.U[3] = ginitial_state.U[6];
   */
  
   
   
  
  times( &end );
  TIME( grelev_time );

  times( &start );

  /* now build globally accessable connectivity graph
     构建全局可访问的连接图
     1000行代码
     构建各个fact和effect之间的关系，以及哪些action会产生哪些effect（effect表示为删除哪些fact，加入哪些fact）
   */
  build_connectivity_graph();

  /*测试输出*/
  print_state(ginitial_state_old);

  times( &end );
  TIME( gconn_time );

  /***********************************************************
   * we are finally through with preprocessing and can worry *
   * bout finding a plan instead.    
   * 开始考虑如何找到一个解决方案   
   * 这一部分用函数initSomeVar()表示                     *
   ***********************************************************/

  // times( &start );

  // /* 2 * #initial equivalences plus #initial OR clauses plus
  //  * max ops to induce * (max ef implic of op<最大效果隐含数> * max noop implic) plus
  //  * max #additional clauses for conflict check plus
  //  * max #additional clauses for infer clauses
  //  */
  // /*计算会有的clause最大数量*/
  // gmax_clauses = 
  //   (2 * gnum_initial_equivalence) +
  //   (MAX_PLAN_LENGTH * (gmax_E + (2 * gmax_CNFU))) +
  //   gmax_C * 2 +
  //   1;
  // for ( i = 0; i < gnum_initial_or; i++ ) {
  //   /* all ordered pairs of fts yield one binary clause.
  //     对于所有的有序配对的fts（符号翻译集合），会产生一个二元子句
  //    */
  //   gmax_clauses += ginitial_or_length[i] * (ginitial_or_length[i] - 1);
  // }
  // /*printf("gmax_clauses:%d\n",gmax_clauses);*/
  // /* 2 * #initial equivalences plus #initial OR clauses plus
  //  * 2 * [as we got two cnfs glued together] max ops to induce * 
  //  * (max ef implic of op * max noop implic) plus
  //  * max #additional clauses for improvement clauses
  //  */
  // gmax_rs_clauses = 
  //   (2 * gnum_initial_equivalence) +
  //   (2 * MAX_PLAN_LENGTH * (gmax_E + (2 * gmax_CNFU))) +
  //   2;
  // for ( i = 0; i < gnum_initial_or; i++ ) {
  //   /* all ordered pairs of fts yield one binary clause.
  //     这些也会产生子句
  //    */
  //   gmax_rs_clauses += ginitial_or_length[i] * (ginitial_or_length[i] - 1);
  // }

  // /* max. size effect axiom
  //  */ 
  // gmax_literals = gmax_C + 1;
  // /* if all effs of maxE op contradict with the same fact then
  //  * the resulting noop clause is this long.
  //  */ 
  // if ( gmax_E + 2 > gmax_literals ) {
  //   gmax_literals = gmax_E + 2;
  // }
  // /* ini OR lengths...
  //  */
  // for ( i = 0; i < gnum_initial_or; i++ ) {
  //   if ( ginitial_or_length[i] > gmax_literals ) {
  //     gmax_literals = ginitial_or_length[i];
  //   }
  // }

  // /* make space in plan states info, and relax; don't count the time for that.
  //  */
  // for ( i = 0; i < MAX_PLAN_LENGTH + 1; i++ ) {
  //   /*gnum_ft_conn 最终fact的数量*/
  //   make_state( &(gplan_states[i]), gnum_ft_conn );
  // }
  // /*为规划算法中使用的各种全局数组分配内存*/
  // initialize_state_transitions();
  // /*生成规划算法中使用的子句，以便在后续的规划过程中使用*/
  // extend_fixed_clauses_base( 0, 0 );
  // /*为每个子句中的文字（literal）分配一个唯一的编码，以便在后续的推理过程中使用*/
  // extend_fixed_clauses_base_encoding( 0 );
  // /*简化或放宽问题的约束条件，以便更容易地解决问题*/
  // /*用于创建各种数据结构和初始化变量，以便后续的规划算法可以进行有效的推理和搜索*/
  // initialize_relax();
  // if ( gcmd_line.dominating ) {
  //   initialize_repeated_states();
  // }
  // source_to_dest( &(gplan_states[0]), &ginitial_state );

  // times( &end );
  // TIME( gmem_time );

  times( &start );

  if ( gcmd_line.manual ) {
    if ( gcmd_line.debug == 0 ) {
      gcmd_line.debug = 1;
    }
    manual_control();
    printf("\n\n");
    exit( 0 );
  }
  /*
    1 对于初始状态的处理以及表示方式
    2 对于反例应该如何得到，即对于一个plan是怎样验证的，而对怎么判断这个规划是否能解
  */
  found_plan = FALSE;
  // State testinit = ginitial_state,goal = ggoal_state;
  /*
  ginitial_state.num_U=5;
  ginitial_state.F=(int *)malloc(5*sizeof(int));
  ginitial_state.num_F=1;
  ginitial_state.F[0]=10;
  */
  printf("/n输出初始状态");
  print_state(ginitial_state);
 /* printf("maxF:%d\n",ginitial_state.max_F);
  printf("\n");
*/
  printf("---------\n目标状态");
  print_state(ggoal_state);
  // printf("\n");
  // printf("---------\n");

  /*第一次要更新设置初始状态为空*/
  initGinitiaState();
  initSomeVar();
  /*存储反例*/
  int *ce = (int*)calloc(10000,sizeof(int));
  memset(ce,0,10000);
  int celen=0;
  /*在开始规划前，预填入反例*/
  times(&start);
  conputerCounter(ce,&celen);
  addCounter(ce,celen);
  times(&end);
  TIME(gcounter_time);
  int iteration=0,j;
  /*plan*/
  {
    for(;;){
      iteration++;
      printf("\n第%d次迭代\n当前初始状态:\n",iteration);
      print_state(ginitial_state);
      printf("F:%d U:%d\n",ginitial_state.num_F,ginitial_state.num_U);
      // printf("\n\n----------------------INITIAL ORS:-----------------------------");
      printf("num_Or:%d\n",gnum_initial_or);
      printf("OR: \n");
      for (i = 0; i < gnum_initial_or; i++)
      {
        
        // if(ginitial_or_length[i]>2){
          for (j = 0; j < ginitial_or_length[i]; j++)
          {
            print_ft_name(ginitial_or[i][j]);
            printf(" ");
          }
          printf("\n");
        // }
          

      }
      if ( gcmd_line.ehc ) {
        /*这个初始状态可以是样本，就是根据这个ginitial_state进行搜索plan*/
        
        found_plan = do_enforced_hill_climbing( &ginitial_state, &ggoal_state );
      }
      /*默认就是强制爬山和最佳优先搜索*/
      if ( !found_plan ) {
          if ( gcmd_line.ehc ) {
        printf("\n\nEnforced Hill-climbing failed !");
        printf("\nswitching to Best-first Search now.\n");
          }
        gnum_plan_ops = 0;
        found_plan = do_best_first_search();
      } 

      times( &end );
      TIME( gsearch_time );

      if ( found_plan ) {
        // print_plan();
        printf("\n\nff: found legal plan as follows");
        printf("\n规划长度：%d\n",gnum_plan_ops);
      }else{
        break;
      }
      // output_planner_info();
      times(&start);
      /*重新找到反例，贪婪增加初始集的大小*/
      if(conputerCounter(ce,&celen)){
          printf("找到反例！\n");
          /*释放此次迭代申请的空间*/
          freesomeVar();
          addCounter(ce,celen);
          times(&end);
          TIME(gcounter_time);
          /*感觉初始集初始化规划器*/
          initSomeVar();
          printf("\n");
          // for(i=0;i<celen;i++)
          //   printf("%d,",ce[i]);
          // printf("\n");
      }else{
        times(&end);
        TIME(gcounter_time);
        printf("没有反例，找到最终解！\n");
        break;
      }
    }

  }
  printf("\n\n");
  if ( found_plan ) {
        print_plan();
  }else{
    printf("规划器未寻找到规划解!\n");
  }
  output_planner_info();
  /*初始的初始状态以及目标状态*/
  printf("\n初始目标状态\n");
  printf("Fold:%d Uold:%d\n",ginitial_state_old.num_F,ginitial_state_old.num_U);
  // printf("\n\n----------------------INITIAL ORS:-----------------------------");
  printf("num_Orold:%d\n",gnum_initial_or_old);
  printf("参数大于2的OR: \n");
  for (i = 0; i < gnum_initial_or_old; i++)
  {
    
    if(ginitial_or_length_old[i]>2){
      for (j = 0; j < ginitial_or_length_old[i]; j++)
      {
        print_ft_name(ginitial_or_old[i][j]);
        printf(" ");
      }
      printf("\n");
    }
      
  }
  /*当前反例添加的目标状态*/
  printf("\n\n当前反例添加的目标状态\n");
  printf("Fcur:%d Ucur:%d\n",ginitial_state.num_F,ginitial_state.num_U);
      // printf("\n\n----------------------INITIAL ORS:-----------------------------");
  printf("num_Orcur:%d\n",gnum_initial_or);
  printf("参数大于2的OR: \n");
  for (i = 0; i < gnum_initial_or; i++)
  {
    
    if(ginitial_or_length[i]>2){
      for (j = 0; j < ginitial_or_length[i]; j++)
      {
        print_ft_name(ginitial_or[i][j]);
        printf(" ");
      }
      printf("\n");
    }
      
  }
  printf("\n");
  printf("\ncounter_time:%.2f",gcounter_time);
  printf("\nplan length:%d\niteration:%d\n",gnum_plan_ops,iteration);

  /*测试neg_string每次迭代的重置*/
  /*
  for(i=0;i<=3;i++){
    test111(i);
  }
  */
  exit( 0 );

}
























/*
 *  ----------------------------- HELPING FUNCTIONS ----------------------------
 */






























void output_planner_info( void )

{

  int i;

  printf( "\n\nstatistics: %7.2f seconds instantiating %d easy, %d hard action templates", 
	  gtempl_time, gnum_easy_templates, gnum_hard_mixed_operators );
  printf( "\n            %7.2f seconds reachability analysis, yielding %d facts and %d actions", 
	  greach_time, gnum_pp_facts, gnum_actions );
  printf( "\n            %7.2f seconds creating final representation with %d relevant facts (%d max U, %d CNF max U)", 
	  grelev_time, gnum_relevant_facts, gmax_U, gmax_CNFU );
  printf( "\n            %7.2f seconds building connectivity graph",
	  gconn_time );



  printf( "\n            %7.2f seconds (%7.2f pure) evaluating %d states, to a max depth of %d",
	  geval_time + gr_sat_time + grp_sat_time + gr_cnf_time + gr_enc_time, 
	  geval_time, gevaluated_states, gmax_search_depth );
  if ( gcmd_line.heuristic == 1 ) {
    printf( "\n            %7.2f seconds in DP for %d RPG ini state implication checks", 
	    gr_sat_time, gr_sat_calls );
    printf( "\n            %7.2f seconds in DP for %d RPlan extract ini state implication checks (%d lits removed)", 
	    grp_sat_time, grp_sat_calls, gremoved_lits );
  }
  if ( gcmd_line.heuristic == 2 ) {
    printf( "\n            %7.2f seconds generating, %7.2f seconds encoding Rplan S-CNFs",
	    gr_cnf_time, gr_enc_time);
    printf( "\n            %7.2f seconds in DP for %d RPG S-CNF implication checks", 
	    gr_sat_time, gr_sat_calls );
    printf( "\n            %7.2f seconds in DP for %d RPlan extract S-CNF implication checks (%d lits removed)", 
	    grp_sat_time, grp_sat_calls, gremoved_lits );
  }



  printf( "\n            %7.2f seconds generating, %7.2f seconds encoding %d state transition base CNFs",
	  gcnf_time, genc_time, gcnfs);
  printf( "\n            %7.2f seconds in DP solving %d state transition CNFs", 
	  gsat_time, gsat_calls );
  printf( "\n            %7.2f seconds checking for self-contradictions, including %d DP calls", 
	  gsc_time, gsc_sat_calls );
  if ( gcmd_line.stagnating ) {
    printf( "\n            %7.2f seconds checking for stagnating states (%d hits), including %d DP calls", 
	    gss_time, gss_hits, gss_sat_calls );
  }
  if ( gcmd_line.dominating ) {
    printf( "\n            %7.2f seconds altogether checking for dominated states making %d comparisons (%d conformant, %d hits),\n                    spending %7.2f seconds doing %d DP calls", 
	    grs_time + grs_sat_time, grs_comps, grs_conf_comps, grs_hits, grs_sat_time, grs_sat_calls );
  }
  printf( "\n            %7d total DP calls, %d total UP calls, %7.2f sec membership", 
	  gdp_calls, gup_calls, gmembership_time);
  if ( gcmd_line.debug ) {
    printf("\n                CNF statistics:");
    for ( i = 0; i < gmax_literals + 1; i++ ) {
      printf(" %d:%.2f", i, ((float) gsum_k_clauses[i])/((float) gsum_clauses));
    }
  }
  printf( "\n            %7.2f seconds for remaining searching duties",
	  gsearch_time);
  printf( "\n            %7.2f seconds total time (+ %7.2f secs for CNF memory allocation)\n", 
	  gtempl_time + greach_time + grelev_time + gconn_time + genc_time + gsearch_time + gsat_time + geval_time + gr_sat_time + grp_sat_time + gr_cnf_time + gr_enc_time + gcnf_time + grs_time + gss_time + grs_sat_time, gmem_time);


}



void ff_usage( void )

{

  printf("\nUsage of Conformant-FF:\n");

  printf("\nOPTIONS   DESCRIPTIONS\n\n");
  printf("-p <str>    path for operator and fact file\n");
  printf("-o <str>    operator file name\n");
  printf("-f <str>    fact file name\n\n");

  printf("-h <num>    heuristic function to be used (preset: %d) (explanation: see journal paper)\n", 
	 gcmd_line.heuristic);
  printf("      0     implication graph for path to s plus RPG, incomplete check for leafs implication by I\n");
  printf("      1     implication graph for path to s plus RPG, complete check for leafs implication by I\n");
  printf("      2     implication graph for RPG, complete check for leafs implication by phi(s)\n\n");

  printf("-E          EHC run OFF\n");
  printf("-H          helpful actions OFF\n\n");

  printf("-S          stagnating paths check OFF\n");
  printf("-D          full repeated (dominated) states check OFF\n\n");

  printf("-B          run Best-first search in breadth-first style\n\n");

  printf("-M          manual search control\n");
  printf("-d <num>    debug info level (preset %d)\n", gcmd_line.debug);
  printf("-R          debug relax.c\n");
  printf("-A          debug search.c\n");
  printf("-T          debug state_transitions.cpp\n");
  printf("-P          debug repeated_states.cpp\n\n");

  if ( 0 ) {
    printf("-i <num>    run-time information level( preset: 1 )\n");
    printf("      0     only times\n");
    printf("      1     problem name, planning process infos\n");
    printf("    101     parsed problem data\n");
    printf("    102     cleaned up ADL problem\n");
    printf("    103     collected string tables\n");
    printf("    104     encoded domain\n");
    printf("    105     predicates inertia info\n");
    printf("    106     splitted initial state\n");
    printf("    107     domain with Wff s normalized\n");
    printf("    108     domain with NOT conds translated\n");
    printf("    109     splitted domain\n");
    printf("    110     cleaned up easy domain\n");
    printf("    111     unaries encoded easy domain\n");
    printf("    112     effects multiplied easy domain\n");
    printf("    113     inertia removed easy domain\n");
    printf("    114     easy action templates\n");
    printf("    115     cleaned up hard domain representation\n");
    printf("    116     mixed hard domain representation\n");
    printf("    117     final hard domain representation\n");
    printf("    118     reachability analysis results\n");
    printf("    119     facts selected as relevant\n");
    printf("    120     final domain and problem representations\n");
    printf("    121     connectivity graph\n");
    printf("    122     fixpoint result on each evaluated state\n");
    printf("    123     1P extracted on each evaluated state\n");
    printf("    124     H set collected for each evaluated state\n");
    printf("    125     False sets of goals <GAM>\n");
    printf("    126     detected ordering constraints leq_h <GAM>\n");
    printf("    127     the Goal Agenda <GAM>\n");
  }

}



Bool process_command_line( int argc, char *argv[] )

{

  char option;

  while ( --argc && ++argv ) {
    if ( *argv[0] != '-' || strlen(*argv) != 2 ) {
      return FALSE;
    }
    option = *++argv[0];
    switch ( option ) {
    case 'M':
      gcmd_line.manual = TRUE;
      break;
    case 'E':
      gcmd_line.ehc = FALSE;
      break;
    case 'H':
      gcmd_line.help = FALSE;
      break;
    case 'S':
      gcmd_line.stagnating = FALSE;
      break;
    case 'D':
      gcmd_line.dominating = FALSE;
      break;
    case 'B':
      gcmd_line.breadth_bfs = TRUE;
      break;
    case 'R':
      gcmd_line.R = TRUE;
      break;
    case 'A':
      gcmd_line.A = TRUE;
      break;
    case 'T':
      gcmd_line.T = TRUE;
      break;
    case 'P':
      gcmd_line.P = TRUE;
      break;
    default:
      if ( --argc && ++argv ) {
	switch ( option ) {
	case 'p':
	  strncpy( gcmd_line.path, *argv, MAX_LENGTH );
	  break;
	case 'o':
	  strncpy( gcmd_line.ops_file_name, *argv, MAX_LENGTH );
	  break;
	case 'f':
	  strncpy( gcmd_line.fct_file_name, *argv, MAX_LENGTH );
	  break;
	case 'i':
	  sscanf( *argv, "%d", &gcmd_line.display_info );
	  break;
	case 'h':
	  sscanf( *argv, "%d", &gcmd_line.heuristic );
	  break;
	case 'd':
	  sscanf( *argv, "%d", &gcmd_line.debug );
	  break;
	default:
	  printf( "\nff: unknown option: %c entered\n\n", option );
	  return FALSE;
	}
      } else {
	return FALSE;
      }
    }
  }

  if ( gcmd_line.heuristic < 0 || gcmd_line.heuristic > 3 ) {
    printf( "\nunknown heuristic function, %d\n\n", gcmd_line.heuristic );
    return FALSE;
  }
  return TRUE;

}

