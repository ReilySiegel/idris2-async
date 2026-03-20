module IO.Async.Mutex

import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Queue
import IO.Async
import Syntax.T1

%default total

record Locker where
  constructor L
  token    : Token World
  callback : IO1 ()

Eq Locker where v1 == v2 = v1.token == v2.token

data ST : Type where
  Unlocked : ST
  Locked : Queue Locker -> ST

export
record Mutex where
  constructor M
  ref : IORef ST

export %inline
mutex : Lift1 World f => f Mutex
mutex = M <$> newref Unlocked

takeL : Locker -> IO1 (IO1 ())
takeL (L _ cb) t = let _ # t := cb t in unit1 # t

cancelLock : IORef ST -> Locker -> IO1 ()
cancelLock r l = casmod1 r $ \case
  Unlocked => Unlocked
  Locked q => Locked $ filter (/= l) q

lock1 : IORef ST -> Locker -> IO1 (IO1 ())
lock1 r lk t = let act # t := casupdate1 r adj t in act t
  where
    adj : ST -> (ST, IO1 (IO1 ()))
    adj Unlocked   = (Locked empty, takeL lk)
    adj (Locked q) = (Locked (enqueue q lk), pure $ cancelLock r lk)

unlock1 : IORef ST -> IO1 ()
unlock1 ref t = let act # t := casupdate1 ref adj t in act t
  where
    adj : ST -> (ST, IO1 ())
    adj Unlocked   = (Unlocked, pure ())
    adj (Locked q) = case dequeue q of
      Just ((L _ cb), q2) => (Locked q2, cb)
      Nothing       => (Unlocked, pure ())

export
lock : Mutex -> Async e es ()
lock (M ref) =
  primAsync $ \cb,t =>
    let tok # t := token1 t
    in lock1 ref (L tok $ cb (Right ())) t

export
unlock : Mutex -> Async e es ()
unlock (M ref) = lift1 $ unlock1 ref
