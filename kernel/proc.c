#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"
typedef long long ll;

/* Period parameters */
#define N 624
#define M 397
#define MATRIX_A 0x9908b0df   /* constant vector a */
#define UPPER_MASK 0x80000000 /* most significant w-r bits */
#define LOWER_MASK 0x7fffffff /* least significant r bits */

/* Tempering parameters */
#define TEMPERING_MASK_B 0x9d2c5680
#define TEMPERING_MASK_C 0xefc60000
#define TEMPERING_SHIFT_U(y) (y >> 11)
#define TEMPERING_SHIFT_S(y) (y << 7)
#define TEMPERING_SHIFT_T(y) (y << 15)
#define TEMPERING_SHIFT_L(y) (y >> 18)

#define RAND_MAX 0x7fffffff

static unsigned long mt[N]; /* the array for the state vector  */
static int mti = N + 1;     /* mti==N+1 means mt[N] is not initialized */

struct cpu cpus[NCPU];

struct proc proc[NPROC];

struct proc *initproc;

int nextpid = 1;
struct spinlock pid_lock;
int totaltickets = 0;
extern void forkret(void);
static void freeproc(struct proc *p);

extern char trampoline[]; // trampoline.S

// helps ensure that wakeups of wait()ing
// parents are not lost. helps obey the
// memory model when using p->parent.
// must be acquired before any p->lock.
struct spinlock wait_lock;

void sgenrand(unsigned long seed)
{
  mt[0] = seed & 0xffffffff;
  for (mti = 1; mti < N; mti++)
  {
    mt[mti] = (69069 * mt[mti - 1]) & 0xffffffff;
  }
}

long genrand()
{
  unsigned long y;
  static unsigned long mag01[2] = {0x0, MATRIX_A};
  /* mag01[x] = x * MATRIX_A  for x=0,1 */

  if (mti >= N)
  { /* generate N words at one time */

    if (mti == 625) /* if sgenrand() has not been called, */
    {
      sgenrand(4357); /* a default initial seed is used   */
    }
    int kk;
    kk = 0;
    int diff;
    diff = N - M;
    for (; kk < diff; kk++)
    {
      y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
      mt[kk] = mt[kk + M] ^ (y >> 1) ^ mag01[y & 0x1];
    }
    for (; kk < N - 1; kk++)
    {
      y = (mt[kk] & UPPER_MASK) | (mt[kk + 1] & LOWER_MASK);
      mt[kk] = mt[kk + (M - N)] ^ (y >> 1) ^ mag01[y & 0x1];
    }
    y = (mt[N - 1] & UPPER_MASK) | (mt[0] & LOWER_MASK);
    mt[N - 1] = mt[M - 1] ^ (y >> 1) ^ mag01[y & 0x1];

    mti = 0;
  }

  y = mt[mti++];
  y ^= TEMPERING_SHIFT_U(y);
  y ^= TEMPERING_SHIFT_S(y) & TEMPERING_MASK_B;
  y ^= TEMPERING_SHIFT_T(y) & TEMPERING_MASK_C;
  y ^= TEMPERING_SHIFT_L(y);

  // Strip off uppermost bit because we want a long,
  // not an unsigned long
  return y & RAND_MAX;
}

// Assumes 0 <= max <= RAND_MAX
// Returns in the half-open interval [0, max]
long random_at_most(long max)
{
  unsigned long
      // max <= RAND_MAX < ULONG_MAX, so this is okay.
      num_bins = (unsigned long)max + 1,
      num_rand = (unsigned long)RAND_MAX + 1,
      bin_size = num_rand / num_bins,
      defect = num_rand % num_bins;

  long x;
  do
  {
    x = genrand();
  }
  // This is carefully written not to overflow
  while (num_rand - defect <= (unsigned long)x);

  // Truncated division is intentional
  return x / bin_size;
}

// Allocate a page for each process's kernel stack.
// Map it high in memory, followed by an invalueid
// guard page.
void proc_mapstacks(pagetable_t kpgtbl)
{
  struct proc *p;

  for (p = proc; p < &proc[NPROC]; p++)
  {
    char *pa = kalloc();
    if (pa == 0)
      panic("kalloc");
    uint64 va = KSTACK((int)(p - proc));
    kvmmap(kpgtbl, va, (uint64)pa, PGSIZE, PTE_R | PTE_W);
  }
}

// initialize the proc table.
void procinit(void)
{
  struct proc *p;

  initlock(&pid_lock, "nextpid");
  initlock(&wait_lock, "wait_lock");
  for (p = proc; p < &proc[NPROC]; p++)
  {
    initlock(&p->lock, "proc");
    // p->state = UNUSED;
    p->kstack = KSTACK((int)(p - proc));
  }
}

// Must be called with interrupts disabled,
// to prevent race with process being moved
// to a different CPU.
int cpuid()
{
  int id = r_tp();
  return id;
}

// Return this CPU's cpu struct.
// Interrupts must be disabled.
struct cpu *
mycpu(void)
{
  int id = cpuid();
  struct cpu *c = &cpus[id];
  return c;
}

// Return the current struct proc *, or zero if none.
struct proc *
myproc(void)
{
  push_off();
  struct cpu *c = mycpu();
  struct proc *p = c->proc;
  pop_off();
  return p;
}

int allocpid()
{
  int pid;

  acquire(&pid_lock);
  pid = nextpid;
  nextpid = nextpid + 1;
  release(&pid_lock);

  return pid;
}

// Look in the process table for an UNUSED proc.
// If found, initialize state required to run in the kernel,
// and return with p->lock held.
// If there are no free procs, or a memory allocation fails, return 0.
static struct proc *
allocproc(void)
{
  struct proc *p;

  for (p = proc; p < &proc[NPROC]; p++)
  {
    acquire(&p->lock);
    if (p->state == UNUSED)
    {
      goto found;
    }
    else
    {
      release(&p->lock);
    }
  }
  return 0;

found:
  p->pid = allocpid();
  p->state = USED;
  p->staticPriority = 60;

  // Allocate a trapframe page.
  if ((p->trapframe = (struct trapframe *)kalloc()) == 0)
  {
    freeproc(p);
    release(&p->lock);
    return 0;
  }

  // An empty user page table.
  p->pagetable = proc_pagetable(p);
  if (p->pagetable == 0)
  {
    freeproc(p);
    release(&p->lock);
    return 0;
  }
  p->create_time = ticks;
  p->nosch = 0;
  p->etime = 0;
  p->rtime = 0;
  // Set up new context to start executing at forkret,
  // which returns to user space.
  memset(&p->context, 0, sizeof(p->context));
  p->context.ra = (uint64)forkret;
  p->context.sp = p->kstack + PGSIZE;
  p->cur_ticks = 0;
  p->schedt = 0;
  p->tickets = 1;
#ifdef MLFQ

  p->en_time = ticks;
  p->curr_queue = 0;
  int i;
  i = 0;
  for (; i < 5; i++)
  {
    p->queue_tck[i] = 0;
  }
#endif
  return p;
}

// free a proc structure and the data hanging from it,
// including user pages.
// p->lock must be held.
static void
freeproc(struct proc *p)
{
  if (p->trapframe)
    kfree((void *)p->trapframe);
  p->trapframe = 0;
  if (p->pagetable)
    proc_freepagetable(p->pagetable, p->sz);
  p->pagetable = 0;
  p->sz = 0;
  p->pid = 0;
  p->parent = 0;
  p->name[0] = 0;
  p->chan = 0;
  p->killed = 0;
  p->xstate = 0;
  p->state = UNUSED;
  p->tickets = 0;
}

// Create a user page table for a given process, with no user memory,
// but with trampoline and trapframe pages.
pagetable_t
proc_pagetable(struct proc *p)
{
  pagetable_t pagetable;

  // An empty page table.
  pagetable = uvmcreate();
  if (pagetable == 0)
    return 0;

  // map the trampoline code (for system call return)
  // at the highest user virtual address.
  // only the supervisor uses it, on the way
  // to/from user space, so not PTE_U.
  if (mappages(pagetable, TRAMPOLINE, PGSIZE,
               (uint64)trampoline, PTE_R | PTE_X) < 0)
  {
    uvmfree(pagetable, 0);
    return 0;
  }

  // map the trapframe page just below the trampoline page, for
  // trampoline.S.
  if (mappages(pagetable, TRAPFRAME, PGSIZE,
               (uint64)(p->trapframe), PTE_R | PTE_W) < 0)
  {
    uvmunmap(pagetable, TRAMPOLINE, 1, 0);
    uvmfree(pagetable, 0);
    return 0;
  }

  return pagetable;
}

// Free a process's page table, and free the
// physical memory it refers to.
void proc_freepagetable(pagetable_t pagetable, uint64 sz)
{
  uvmunmap(pagetable, TRAMPOLINE, 1, 0);
  uvmunmap(pagetable, TRAPFRAME, 1, 0);
  uvmfree(pagetable, sz);
}

// a user program that calls exec("/init")
// assembled from ../user/initcode.S
// od -t xC ../user/initcode
uchar initcode[] = {
    0x17, 0x05, 0x00, 0x00, 0x13, 0x05, 0x45, 0x02,
    0x97, 0x05, 0x00, 0x00, 0x93, 0x85, 0x35, 0x02,
    0x93, 0x08, 0x70, 0x00, 0x73, 0x00, 0x00, 0x00,
    0x93, 0x08, 0x20, 0x00, 0x73, 0x00, 0x00, 0x00,
    0xef, 0xf0, 0x9f, 0xff, 0x2f, 0x69, 0x6e, 0x69,
    0x74, 0x00, 0x00, 0x24, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00};

// Set up first user process.
void userinit(void)
{
  struct proc *p;

  p = allocproc();
  initproc = p;

  // allocate one user page and copy initcode's instructions
  // and data into it.
  uvmfirst(p->pagetable, initcode, sizeof(initcode));
  p->sz = PGSIZE;

  // prepare for the very first "return" from kernel to user.
  p->trapframe->epc = 0;     // user program counter
  p->trapframe->sp = PGSIZE; // user stack pointer

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;

  release(&p->lock);
}

// Grow or shrink user memory by n bytes.
// Return 0 on success, -1 on failure.
int growproc(int n)
{
  uint64 sz;
  struct proc *p = myproc();

  sz = p->sz;
  if (n > 0)
  {
    if ((sz = uvmalloc(p->pagetable, sz, sz + n, PTE_W)) == 0)
    {
      return -1;
    }
  }
  else if (n < 0)
  {
    sz = uvmdealloc(p->pagetable, sz, sz + n);
  }
  p->sz = sz;
  return 0;
}

// Create a new process, copying the parent.
// Sets up child kernel stack to return as if from fork() system call.
int fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *p = myproc();

  // Allocate process.
  if ((np = allocproc()) == 0)
  {
    return -1;
  }
  np->mask = p->mask;

  // Copy user memory from parent to child.
  if (uvmcopy(p->pagetable, np->pagetable, p->sz) < 0)
  {
    freeproc(np);
    release(&np->lock);
    return -1;
  }
  np->sz = p->sz;

  // copy saved user registers.
  *(np->trapframe) = *(p->trapframe);

  // Cause fork to return 0 in the child.
  np->trapframe->a0 = 0;

  // increment reference counts on open file descriptors.
  for (i = 0; i < NOFILE; i++)
    if (p->ofile[i])
      np->ofile[i] = filedup(p->ofile[i]);
  np->cwd = idup(p->cwd);

  safestrcpy(np->name, p->name, sizeof(p->name));

  pid = np->pid;

  release(&np->lock);

  acquire(&wait_lock);
  np->parent = p;
  np->schedt = p->schedt;
  totaltickets += np->tickets;
  release(&wait_lock);

  acquire(&np->lock);
  np->state = RUNNABLE;
  release(&np->lock);

  return pid;
}

// Pass p's abandoned children to init.
// Caller must hold wait_lock.
void reparent(struct proc *p)
{
  struct proc *pp;

  for (pp = proc; pp < &proc[NPROC]; pp++)
  {
    if (pp->parent == p)
    {
      pp->parent = initproc;
      wakeup(initproc);
    }
  }
}
void updateTime()
{
  struct proc *p;
  for (p = proc; p < &proc[NPROC]; p++)
  {
    acquire(&p->lock);
    if (p->state == RUNNING)
    {
      p->rtime++;
      p->total_run_time++;
    }
    if (p->state == SLEEPING)
      p->sleeptime++;
    release(&p->lock);
  }
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait().
void exit(int status)
{
  struct proc *p = myproc();

  if (p == initproc)
    panic("init exiting");

  // Close all open files.
  for (int fd = 0; fd < NOFILE; fd++)
  {
    if (p->ofile[fd])
    {
      struct file *f = p->ofile[fd];
      fileclose(f);
      p->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(p->cwd);
  end_op();
  p->cwd = 0;

  acquire(&wait_lock);

  // Give any children to init.
  reparent(p);

  // Parent might be sleeping in wait().
  wakeup(p->parent);

  acquire(&p->lock);

  p->xstate = status;
  p->state = ZOMBIE;
  p->etime = ticks;
  totaltickets -= p->tickets;
  p->tickets = 0;

  release(&wait_lock);

  // Jump into the scheduler, never to return.
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int wait(uint64 addr)
{
  struct proc *pp;
  int havekids, pid;
  struct proc *p = myproc();

  acquire(&wait_lock);

  for (;;)
  {
    // Scan through table looking for exited children.
    havekids = 0;
    for (pp = proc; pp < &proc[NPROC]; pp++)
    {
      if (pp->parent == p)
      {
        // make sure the child isn't still in exit() or swtch().
        acquire(&pp->lock);

        havekids = 1;
        if (pp->state == ZOMBIE)
        {
          // Found one.
          pid = pp->pid;
          if (addr != 0 && copyout(p->pagetable, addr, (char *)&pp->xstate,
                                   sizeof(pp->xstate)) < 0)
          {
            release(&pp->lock);
            release(&wait_lock);
            return -1;
          }
          freeproc(pp);
          release(&pp->lock);
          release(&wait_lock);
          return pid;
        }
        release(&pp->lock);
      }
    }

    // No point waiting if we don't have any children.
    if (!havekids || killed(p))
    {
      release(&wait_lock);
      return -1;
    }

    // Wait for a child to exit.
    sleep(p, &wait_lock); // DOC: wait-sleep
  }
}

void set_proc_tckts(int n)
{
  acquire(&proc->lock);
  int prctck;
  prctck = proc->tickets;
  totaltickets -= prctck;
  prctck = n;
  totaltickets += prctck;
  release(&proc->lock);
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run.
//  - swtch to start running that process.
//  - eventually that process transfers control
//    via swtch back to the scheduler.
void scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();

  c->proc = 0;
  for (;;)
  {
    // Avoid deadlock by ensuring that devices can interrupt.
    intr_on();
#ifdef RR

    for (p = proc; p < &proc[NPROC]; p++)
    {
      acquire(&p->lock);
      if (p->state == RUNNABLE)
      {
        p->state = RUNNING;
        c->proc = p;

        p->nosch++;
        swtch(&c->context, &p->context);
        c->proc = 0;
      }
      release(&p->lock);
    }

#endif
#ifdef FCFS
    struct proc *process;
    process = 0;
    uint64 tm;
    tm = 0;
    for (p = proc; p < &proc[NPROC]; p++)
    {
      acquire(&p->lock);
      enum procstate run;
      run = p->state;
      if (run == RUNNABLE)
      {
        if ((p->create_time < tm))
        {
          if (process)
          {
            release(&process->lock);
          }
          process = p;
        }
        else if ((!process))
        {
          if (process)
          {
            release(&process->lock);
          }
          process = p;
        }
        else
        {
          release(&p->lock);
        }
      }
      if (p->state != RUNNABLE)
      {
        release(&p->lock);
      }
    }

    if (process)
    {
      process->state = RUNNING;
      c->proc = process;
      swtch(&c->context, &process->context);
      process->nosch++;
      c->proc = 0;
      release(&process->lock);
    }

#endif
#ifdef PBS

    struct proc *process;
    process = 0;
    int dp;
    dp = 101;
    for (p = proc; p < &proc[NPROC]; p++)
    {
      acquire(&p->lock);

      int niceness;
      niceness = 5;
      int pn;
      pn = p->nosch;
      if (pn)
      {
        int pst;
        pst = p->sleeptime;
        int prt;
        prt = p->rtime;
        int tt;
        tt = pst + prt;

        if (tt == 0)
        {
          niceness = 5;
        }
        if (tt != 0)
        {
          niceness = (pst / tt) * 10;
        }
      }

      int priop;
      priop = p->staticPriority;

      int minus;
      minus = niceness - 5;

      int value;
      value = priop - minus;
      int tmp;
      if (value > 100)
        tmp = 100;
      else
        tmp = value;
      int processDp;
      if (tmp < 0)
        processDp = 0;
      else
        processDp = tmp;
      int dp1;
      dp1 = (dp == processDp);
      int pnsh, pcret;
      pnsh = p->nosch;
      pcret = p->create_time;

      enum procstate run;
      run = p->state;

      if (run == RUNNABLE)
      {
        if ((dp1 && pnsh < process->nosch))
        {
          if (process)
            release(&process->lock);

          process = p;
          dp = processDp;
          continue;
        }
        if ((dp1 && pnsh == process->nosch && pcret < process->create_time))
        {
          if (process)
            release(&process->lock);

          process = p;
          dp = processDp;
          continue;
        }
        if (!process)
        {
          if (process)
            release(&process->lock);

          dp = processDp;
          process = p;
          continue;
        }
        if (dp > processDp)
        {
          if (process)
            release(&process->lock);

          dp = processDp;
          process = p;
          continue;
        }
      }
      release(&p->lock);
    }

    if (process)
    {

      process->starttime = ticks;
      process->state = RUNNING;
      process->rtime = 0;
      process->sleeptime = 0;
      process->nosch++;
      c->proc = process;
      swtch(&c->context, &process->context);
      c->proc = 0;
      release(&process->lock);
    }

#endif
#ifdef MLFQ
    {
      struct proc *process;
      process = 0;
      ll niceness;
      niceness = 5;

      for (p = proc; p < &proc[NPROC]; p++)
      {
        enum procstate run;
        run = p->state;

        if (run == RUNNABLE)
        {
          ll pent, diff, pqu;
          pent = p->en_time;
          diff = ticks - pent;
          pqu = p->curr_queue;
          if ((diff > WAITING_LIMIT))
          {
            if (0 < pqu)
            {
              acquire(&p->lock);
              p->queue_tck[pqu] = p->queue_tck[pqu] + diff;
              pent = ticks;
              pqu--;
              release(&p->lock);
            }
          }
        }
      }

      for (p = proc; p < &proc[NPROC]; p++)
      {
        enum procstate run;
        run = p->state;
        ll pent, pqu;
        pent = p->en_time;
        pqu = p->curr_queue;
        if (run == RUNNABLE)
        {
          if (process == 0)
          {
            process = p;
            niceness = process->curr_queue;
          }
          else if (pqu == niceness && pent < process->en_time)
          {
            process = p;
          }
          else if (pqu < niceness)
          {
            process = p;
            niceness = process->curr_queue;
          }
        }
      }

      if (process != 0)
      {
        acquire(&process->lock);
        if (process->state == RUNNABLE)
        {
          process->en_time = ticks;
          process->nosch++;
          c->proc = process;
          process->state = RUNNING;
          swtch(&c->context, &process->context);
          c->proc = 0;
          ll pqt;
          pqt = process->queue_tck[process->curr_queue];
          pqt += (ticks - process->en_time);
        }
        release(&process->lock);
      }
    }
#endif

#ifdef LBS
    const int TICKECT = (genrand() % (100)) + 1;
    int ticket_count;
    ticket_count = 0;

    for (p = proc; p < &proc[NPROC]; p++)
    {
      acquire(&p->lock);
      enum procstate run;
      run = p->state;
      if (run != RUNNABLE)
      {
        int ptck;
        ptck = p->tickets;
        ticket_count += ptck;

        release(&p->lock);
        continue;
      }
      if (ticket_count + p->tickets < TICKECT)
      {
        release(&p->lock);
        continue;
      }
      else if (ticket_count + p->tickets > totaltickets)
      {
        p->state = RUNNING;
      }
      c->proc = p;

      swtch(&c->context, &p->context);

      c->proc = 0;
      release(&p->lock);
      break;
    }
#endif
  }
}

int set_priority(int priority, int pid)
{
  struct proc *p;

  for (p = proc; p < &proc[NPROC]; p++)
  {
    acquire(&p->lock);

    if (p->pid == pid)
    {
      int value = p->staticPriority;
      p->staticPriority = priority;

      p->rtime = 0;
      p->sleeptime = 0;

      release(&p->lock);

      if (value > priority)
        yield();
      return value;
    }
    release(&p->lock);
  }
  return -1;
}

int waitx(uint64 addr, uint *rtime, uint *wtime)
{
  struct proc *np;
  int havekids, pid;
  struct proc *p = myproc();

  acquire(&wait_lock);

  for (;;)
  {
    // Scan through table looking for exited children.
    havekids = 0;
    for (np = proc; np < &proc[NPROC]; np++)
    {
      if (np->parent == p)
      {
        // make sure the child isn't still in exit() or swtch().
        acquire(&np->lock);

        havekids = 1;
        if (np->state == ZOMBIE)
        {
          // Found one.
          pid = np->pid;
          *rtime = np->rtime;
          *wtime = np->etime - np->create_time - np->rtime;
          if (addr != 0 && copyout(p->pagetable, addr, (char *)&np->xstate, sizeof(np->xstate)) < 0)
          {
            release(&np->lock);
            release(&wait_lock);
            return -1;
          }
          freeproc(np);
          release(&np->lock);
          release(&wait_lock);
          return pid;
        }
        release(&np->lock);
      }
    }

    // No point waiting if we don't have any children.
    if (!havekids || p->killed)
    {
      release(&wait_lock);
      return -1;
    }

    // Wait for a child to exit.
    sleep(p, &wait_lock); // DOC: wait-sleep
  }
}

// Switch to scheduler.  Must hold only p->lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->noff, but that would
// break in the few places where a lock is held but
// there's no process.
void sched(void)
{
  int intena;
  struct proc *p = myproc();

  if (!holding(&p->lock))
    panic("sched p->lock");
  if (mycpu()->noff != 1)
    panic("sched locks");
  if (p->state == RUNNING)
    panic("sched running");
  if (intr_get())
    panic("sched interruptible");

  intena = mycpu()->intena;
  swtch(&p->context, &mycpu()->context);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void yield(void)
{
  struct proc *p = myproc();
  acquire(&p->lock);
  p->state = RUNNABLE;
  sched();
  release(&p->lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch to forkret.
void forkret(void)
{
  static int first = 1;

  // Still holding p->lock from scheduler.
  release(&myproc()->lock);

  if (first)
  {
    // File system initialization must be run in the context of a
    // regular process (e.g., because it calls sleep), and thus cannot
    // be run from main().
    first = 0;
    fsinit(ROOTDEV);
  }

  usertrapret();
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();

  // Must acquire p->lock in order to
  // change p->state and then call sched.
  // Once we hold p->lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup locks p->lock),
  // so it's okay to release lk.

  acquire(&p->lock); // DOC: sleeplock1
  release(lk);
  totaltickets -= p->tickets;
  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  release(&p->lock);
  acquire(lk);
}

// Wake up all processes sleeping on chan.
// Must be called without any p->lock.
void wakeup(void *chan)
{
  struct proc *p;

  for (p = proc; p < &proc[NPROC]; p++)
  {
    if (p != myproc())
    {
      acquire(&p->lock);
      if (p->state == SLEEPING && p->chan == chan)
      {
        p->state = RUNNABLE;
      }
      release(&p->lock);
    }
  }
}

// Kill the process with the given pid.
// The victim won't exit until it tries to return
// to user space (see usertrap() in trap.c).
int kill(int pid)
{
  struct proc *p;

  for (p = proc; p < &proc[NPROC]; p++)
  {
    acquire(&p->lock);
    if (p->pid == pid)
    {
      p->killed = 1;
      if (p->state == SLEEPING)
      {
        // Wake process from sleep().
        p->state = RUNNABLE;
      }
      release(&p->lock);
      return 0;
    }
    release(&p->lock);
  }
  return -1;
}

void setkilled(struct proc *p)
{
  acquire(&p->lock);
  p->killed = 1;
  release(&p->lock);
}

int killed(struct proc *p)
{
  int k;

  acquire(&p->lock);
  k = p->killed;
  release(&p->lock);
  return k;
}

// Copy to either a user address, or kernel address,
// depending on usr_dst.
// Returns 0 on success, -1 on error.
int either_copyout(int user_dst, uint64 dst, void *src, uint64 len)
{
  struct proc *p = myproc();
  if (user_dst)
  {
    return copyout(p->pagetable, dst, src, len);
  }
  else
  {
    memmove((char *)dst, src, len);
    return 0;
  }
}

// Copy from either a user address, or kernel address,
// depending on usr_src.
// Returns 0 on success, -1 on error.
int either_copyin(void *dst, int user_src, uint64 src, uint64 len)
{
  struct proc *p = myproc();
  if (user_src)
  {
    return copyin(p->pagetable, dst, src, len);
  }
  else
  {
    memmove(dst, (char *)src, len);
    return 0;
  }
}

// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void procdump(void)
{
  static char *states[] = {
      [UNUSED] "unused",
      [USED] "used",
      [SLEEPING] "sleep ",
      [RUNNABLE] "runble",
      [RUNNING] "run   ",
      [ZOMBIE] "zombie"};
  struct proc *p;
  char *state;
  printf("\n");

#ifdef PBS
  printf("PID   Priority\tState\t rtime\t wtime\tnrun\n");
#endif

#ifdef FCFS
  printf("PID  \tState\t etime\t create_time\tnrun\n");
#endif
#ifdef RR
  printf("PID   State\t  rtime\t wtime\tnrun\n");
#endif
#ifdef MLFQ
  printf("\nPID\tPriority\tState\trtime\twtime\tnruns\tq0\tq1\tq2\tq3\tq4\n");
#endif
#ifdef LBS
  printf("PID\tState\tTickets\tetime\n");
#endif
  for (p = proc; p < &proc[NPROC]; p++)
  {
    if (p->state == UNUSED)
      continue;
    if (p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";

    ll time;
    ll te, tc, tr;
    te = p->etime;
    tc = p->create_time;
    tr = p->rtime;

    if (te)
    {
      time = te - (tc + tr);
    }
    else
    {
      time = ticks - (tc + tr);
    }

#ifdef PBS
    printf("%d\t%d\t%s    %d\t  %d\t%d", p->pid, p->staticPriority, state, p->rtime, time, p->nosch);
#endif
#ifdef FCFS
    printf("%d\t%s    %d\t     %d   \t %d", p->pid, state, time, p->create_time, p->nosch);
#endif
#ifdef RR
    printf("%d\t%s    %d\t  %d\t%d", p->pid, state, p->rtime, time, p->nosch);
#endif
#ifdef MLFQ
    int end_time;
    end_time = p->etime;
    if (end_time == 0)
    {
      end_time = ticks;
    }

    int curr_queue;
    curr_queue = p->curr_queue;
    if (p->state == ZOMBIE)
    {
      curr_queue = -1;
    }
    printf("%d\t%d\t%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d", p->pid, curr_queue, state, p->rtime, time, p->nosch, p->queue_tck[0], p->queue_tck[1], p->queue_tck[2], p->queue_tck[3], p->queue_tck[4]);
#endif
#ifdef LBS
    printf("%d\t%s\t%d\t%d\n", p->pid, state, p->tickets, time);
#endif
    printf("\n");
  }
}
