# Enhanced xv6
# TVSL Geethika
# Kunkulagunta Anupama

## Spec 1 : System Calls
Added System calls
### Process of adding systemcalls:
1. Add the function's definition to the syscalls.h and syscalls.c files.
2. Put the implementation of the function in the sysproc.c file.
3. Update the remaining files with the legitimate changes necessary for implementation.
4. The functions "proc.h," "proc.c->fork()," "proc.c->allocproc()," and "trap.c->usertrap()" have been modified.
5. All that they do is initialise and update them.
Added syscalls:
### trace
1. Added "strace.c" to the user for syscall testing.
2. Made the necessary modifications to "MAKEFILE" to enable this file's execution.
### sigalarm and sigreturn
1. Added 'alarmtest.c' to the user for syscall testing.
2. Made the necessary modifications to "MAKEFILE" to enable this file's execution.

## Spec 2 : Scheduling
The following are implemented
### FCFS
1. The fundamental idea is to execute the process that was initially created.
2. A new variable is added to the "struct proc" in the "proc.h" file (creation time is noted)
3. Setting the creationtime property to 0 when allocating a process in allocproc
4. By selecting the function with the shortest construction time, the "scheduler()" function is updated.
5. Removing the kerneltrap and usertrap preemption (which is fcfs) from the trap.c file.

### PBS
1. Created a non-prescriptive PBS technique
2. Added some variables to the struct, such as sched time, which indicates how often it is called, and implemented prority, niceness, and sleep time
3. Created new dynamic priority-based scheduling mechanism for PBS in the function "scheduler()."
4. The 'update time' method is used to find the added variables.
5. Created the syscall "set priority," which modifies the process' static priority appropriately.
Running the process with the highest priority follows the fundamental logic.
### MLFQ
1. Implementing queues is one of the prerequisites.
2. New variables, such as the queue used, ticks used, and time spent in each queue
3. These initializations are appropriate.
4. Utilizing five queues
5. Aging is incorporated into the law in acts prematurely
6. The highest priority process is carried out
7. Changes are made in accordance with this in the functions "allocproc," "scheduler()," "clockintr," "kerneltrap," and "usertrap."
8. Only one CPU is being used for testing.

## SCHEDULER Analysis
The timings, wait times, and run times have all been tested.
'waitx' is employed as shown in the tutorial.

## Spec 3 : Copy-on-write fork
### Idea :
1. Initially, both processes that are created by a parent process will share the same memory pages.
2. These pages will be identified as copied-on-write.
3. Copies of the shared pages will be made if any of these processes tries to edit them.
4. Through that method, "modifications will be done on the copy of pages."
5. As a result, the other procedure is unaffected.

### Modifications made :
1. Updated the copyout() and uvmuncopy() routines in vm.c
2. In "trap.c," We declared and used the method "page fault handler()."
3. Added some conditional logic to 'trapinit()' in 'trap.c' based on 'r scause()'
4. In kalloc.c, the functions "init page ref()," "dec page ref()," "inc page ref()," and "get page ref()" were declared and implemented.
5. Used the aforementioned routines in the kalloc.c files "kfree()" and "kinit()."
### cowtest
1. Added 'cowtest.c' to the user for syscall testing.
2. Made the necessary modifications to "MAKEFILE" to enable this file's execution.
