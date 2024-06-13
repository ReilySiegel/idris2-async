# idris2-async: Asynchronous computations in Idris2

This is a library for running cancelable asynchronous computations
with proper error handling in Idris2. Depending on the backend you
use, this also offers true parallelism (computations running in
parallel on multicore systems).

This is a literate Idris source file, so you can compile and run it.
It is recommended to use [pack](https://github.com/stefan-hoeck/idris2-pack)
for building and running the example applications:

```sh
pack -o async exec docs/src/README.md [args]
```

Before we start, let's import a couple of modules:

```idris
module README

import IO.Async
import IO.Async.ThreadPool
import IO.Async.Scheduler
import System

%default total
```

## Introducing the `Async` Monad

This library provides a new data type `Async es a` for providing
asynchronous computations that can fail with one of the errors
listed in `es` and yield a result of type `a` if all goes well.

Before we look at a first example, we need to get our terminology straight.

* synchronous: A sequence of effectful computations is *synchronous*, if
  they produce their results one after the other, in the
  order given by the sequence.
* asynchronous: A sequence of effectful computations is *asynchronous*,
  if the computations seem to be run simultaneously in no clear order.
  Wether they are actually run in parallel on several physical cores
  or still one after the other on a single core is of no importance here.
  What *is* important is that a potentially long running computation
  does not block the whole application so that other computations can
  still be performed.

In order to demonstrate the difference, we define two countdowns:
One for counting down seconds, the other counting down milliseconds
(in 10ms steps):

```idris
countSeconds : Scheduler => Nat -> Async [] ()
countSeconds 0     = putStrLn "Second counter done."
countSeconds (S k) = do
  putStrLn "\{show $ S k} s left"
  sleep 1.s
  countSeconds k

countMillis : Scheduler => Nat -> Async [] ()
countMillis 0     = putStrLn "Millisecond counter done."
countMillis (S k) = do
  putStrLn "\{show $ S k * 10} ms left"
  sleep 10.ms
  countMillis k
```

This is very straight forward: On every recursive step, we *sleep*
for a short amount of time, before continuing the computation. Since
these are `do` blocks, computations are connected via *bind* `(>>=)`,
and this means sequencing computations. Bind will not and cannot change
the order in which the computations are being run, and it will only
proceed to the next computation, when the current one has finished
with a result.

Note, however, that in the examples above there is not blocking of
a physical thread, even though we call `sleep`. I will explain this in
greater details later when we talk about `Fiber`s but for now, suffice
to say that the `sleep` used above (from module `IO.Async.Scheduler.sleep`)
is much more powerful than `System.sleep` from the base library although
the semantically do the same thing: They stop a sequence of computations
for a predefined amount of time.

Let's try and run the two countdowns sequentially:

```idris
countSequentially : Scheduler => Async [] ()
countSequentially = do
  putStrLn "Sequential countdown:"
  countSeconds 2
  countMillis 10
```

You can try this example by running `main` with the `seq` command:

```sh
pack -o async exec docs/src/README.md seq
```

And behold!, the two countdowns will be run one after the other as we would
expect.

Assume now, that the two countdowns are arbitrary long-running computations.
Why should we wait for the first to finish before starting the second, if
they are completely unrelated? Let's try and run them concurrently as we would
with `Prelude.fork`. The primitive to do this is called `start`, and like
`fork`, it returns a value that we can use to wait for the computation
to finish. Here's the code:


```idris
countParallel : Scheduler => Async [] ()
countParallel = do
  f1 <- start $ countSeconds 5
  f2 <- start $ countMillis 300
  joinResult f1
  joinResult f2
```

If you try this example by running `main` with the `par` command, you will
notice that the messages from the two countdowns are now interleaved giving
at least the illusion of concurrency.

Since running several computations and collecting their results
concurrently is such a common thing to do, there is also utility
`par`, which takes a heterogeneous list of computations and
stores their results again in a heterogeneous list (use `"par2"` as the
command-line argument to run this example):

```idris
countParallel2 : Scheduler => Async [] ()
countParallel2 = ignore $ par [ countSeconds 5, countMillis 300 ]
```

Another thing to do with two or more potentially long-running
computations is to run them concurrently until one of them
terminates. This would allow us to - for instance - to run a
long-running computation until a timeout fires, in which case
we might want to end with an error. We will look at that example
later on. For now, let's just run our countdowns concurrently
until the faster of the two terminates (run with command-line
argument `"race"`):

```idris
raceParallel : Scheduler => Async [] ()
raceParallel = race [ countSeconds 5, countMillis 300 ]

act : Scheduler => List String -> Async [] ()
act ("par"   :: _) = countParallel
act ("par2"  :: _) = countParallel2
act ("race"  :: _) = raceParallel
act _              = countSequentially

covering
run : List String -> IO ()
run args = do
  sc <- newSchedulerST
  t  <- fork $ process sc
  app 4 $ act @{sc} args
  stop sc
  threadWait t

covering
main : IO ()
main = do
  _::t <- getArgs | _ => die "Invalid arguments"
  run t
```

<!-- vi: filetype=idris2:syntax=markdown
-->
