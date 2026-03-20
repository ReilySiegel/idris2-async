module IO.Async.Mutex

import Control.Monad.Resource
import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Queue
import IO.Async
import Syntax.T1

%default total

||| A record describing a thread parked on a Mutex.
record Locker where
  constructor L
  token    : Token World
  callback : IO1 ()

Eq Locker where v1 == v2 = v1.token == v2.token

||| Inner state of a Mutex. A Mutex is either Unlocked, or Locked with a
||| potentially empty queue of lockers.
data ST : Type where
  Unlocked : ST
  Locked : Queue Locker -> ST


||| A Mutex.
export
record Mutex where
  constructor M
  ref : IORef ST

||| Creates a new, unlocked Mutex.
export %inline
mutex : Lift1 World f => f Mutex
mutex = M <$> newref Unlocked

takeL : Locker -> IO1 (IO1 ())
takeL (L _ cb) t = let _ # t := cb t in unit1 # t

cancelLock : IORef ST -> Locker -> IO1 ()
cancelLock r l = casmod1 r $ \case
  Unlocked => Unlocked
  Locked q => Locked $ filter (/= l) q

||| Locks a Mutex with the given Locker.
||| Returns an action which cancels the lock.
export
lock1 : IORef ST -> Locker -> IO1 (IO1 ())
lock1 r lk t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST -> (ST, IO1 (IO1 ()))
    adj Unlocked   = (Locked empty, takeL lk)
    adj (Locked q) = (Locked (enqueue q lk), pure $ cancelLock r lk)

||| Unlocks the given Mutex.
export
unlock1 : IORef ST -> IO1 ()
unlock1 ref t = let act # t := casupdate1 ref adj t in act t
  where
    adj : ST -> (ST, IO1 ())
    adj Unlocked   = (Unlocked, pure ())
    adj (Locked q) = case dequeue q of
      Just ((L _ cb), q2) => (Locked q2, cb)
      Nothing       => (Unlocked, pure ())


||| Locks a Mutex.
export
lock : Mutex -> Async e es ()
lock (M ref) =
  primAsync $ \cb,t =>
    let tok # t := token1 t
    in lock1 ref (L tok $ cb (Right ())) t

||| Unlocks a Mutex.
export %inline
unlock : Mutex -> Async e es ()
unlock (M ref) = lift1 $ unlock1 ref

||| A value protected by a Mutex. The inner value can be accessed by
||| `withGuard`, which is similar to `use1`.
export
record Guarded a where
  constructor G
  ref : a
  mut : Mutex

%inline
Resource (Async e) (Guarded a) where
  cleanup (G ref mut) = unlock mut

||| Use a Guarded value protected by a Mutex. Runs `f` when the Mutex lock is
||| succesfully acquired. Automatically unlocks the Mutex when the async action
||| is completed.
export %inline
withGuard : Guarded a -> (a -> Async e es b) -> Async e es b
withGuard g@(G _ mut) f = use1 (const g <$> unlock mut) (f . ref)
