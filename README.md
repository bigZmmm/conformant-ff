# CFF规划器

环境配置：

（1）安装最新版z3求解器 

（2）安装gcc9与g++9

（3）运行在Ubuntu20.04.2版本

​        修改后的规划器由c语言编写，通过makefile进行编译，下面写的compile是将make clean等命令行集合的批处理脚本。

用法：

（1）./compile编译规划器为可执行文件ff

（2）按照./ff -p <domain文件所在路径> -o <domain文件名> -p <problem文件所在路径> -f <problem文件名>对问题进行运行，如./ff -p /home/planner/Downloads/PlannerBenchmark-main/T1/Conformant/det/logistics/ -o domain.pddl -p /home/planner/Downloads/PlannerBenchmark-main/T1/Conformant/det/logistics/ -f p2-2-2.pddl

