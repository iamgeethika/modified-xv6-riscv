#include "types.h"
#include "riscv.h"
#include "defs.h"
#include "param.h"
#include "memlayout.h"
#include "spinlock.h"
#include "proc.h"
typedef long long ll;
uint64
sys_exit(void)
{
  int n;
  argint(0, &n);
  exit(n);
  return 0; // not reached
}

uint64
sys_getpid(void)
{
  return myproc()->pid;
}

uint64
sys_fork(void)
{
  return fork();
}

uint64
sys_wait(void)
{
  uint64 p;
  argaddr(0, &p);
  return wait(p);
}

// uint64
// sys_waitx(void)
// {
//   uint64 addr, addr1, addr2;
//   uint wtime, rtime;
//   argaddr(0, &addr);
//   argaddr(1, &addr1); // user virtual memory
//   argaddr(2, &addr2);
//   int ret = waitx(addr, &wtime, &rtime);
//   struct proc* p = myproc();
//   if (copyout(p->pagetable, addr1,(char*)&wtime, sizeof(int)) < 0)
//     return -1;
//   if (copyout(p->pagetable, addr2,(char*)&rtime, sizeof(int)) < 0)
//     return -1;
//   return ret;
// }
uint64
sys_waitx(void)
{
  uint64 addr, addr1, addr2;
  uint wtime, rtime;
  argaddr(0, &addr);
  argaddr(1, &addr1); // user virtual memory
  argaddr(2, &addr2);
  int ret = waitx(addr, &wtime, &rtime);
  struct proc* p = myproc();
  if (copyout(p->pagetable, addr1,(char*)&wtime, sizeof(int)) < 0)
    return -1;
  if (copyout(p->pagetable, addr2,(char*)&rtime, sizeof(int)) < 0)
    return -1;
  return ret;
}
uint64
sys_sbrk(void)
{
  uint64 addr;
  int n;

  argint(0, &n);
  addr = myproc()->sz;
  if (growproc(n) < 0)
    return -1;
  return addr;
}

uint64
sys_sleep(void)
{
  int n;
  uint ticks0;

  argint(0, &n);
  acquire(&tickslock);
  ticks0 = ticks;
  while (ticks - ticks0 < n)
  {
    if (killed(myproc()))
    {
      release(&tickslock);
      return -1;
    }
    sleep(&ticks, &tickslock);
  }
  release(&tickslock);
  return 0;
}

uint64
sys_kill(void)
{
  int pid;

  argint(0, &pid);
  return kill(pid);
}

// return how many clock tick interrupts have occurred
// since start.
uint64
sys_uptime(void)
{
  uint xticks;

  acquire(&tickslock);
  xticks = ticks;
  release(&tickslock);
  return xticks;
}
uint64
sys_trace()
{
  int mask;

  if (argint(0, &mask) < 0)
    return -1;

  myproc()->mask = mask;
  return 0;
}

uint64 
sys_sigalarm(void)
{
  uint64 addr;
  int ticks;
  ll amptick;
  amptick=argint(0,&ticks);
  
  if(amptick< 0)
  {
    return -1;
  }
  ll argdr;
  argdr= argaddr(1, &addr);

  if(argdr < 0)
  {
    return -1;
  }

  myproc()->ticks = ticks;
  myproc()->handler = addr;

  return 0;
}

uint64 
sys_sigreturn(void)
{
  struct proc *p = myproc();
  const void *k;
  k = p->alarm_tf;
  memmove(p->trapframe, k, PGSIZE);

  kfree(p->alarm_tf);
  p->alarm_tf = 0;
  p->alarm_on = 0;
  p->cur_ticks = 0;
  return p->trapframe->a0;
}

uint64
sys_set_priority()
{
  int pid, priority;
  if(argint(0, &priority) < 0)
  {
    return -1;
  }
  if(argint(1, &pid) < 0)
  {
    return -1;
  }

  return set_priority(priority, pid);
}

int sys_settickets(void)
{
  int no_tick;
  argint(0, &no_tick);
  if(no_tick <= 0)  
    return -1;
  set_proc_tckts(no_tick);


  return 0;
}