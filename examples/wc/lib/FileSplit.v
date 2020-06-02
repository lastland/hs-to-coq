(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require String.
Import String.StringSyntax.
Set Universe Polymorphism.

(* Converted imports: *)

Require Import Control.Monad.
Require Import Data.Foldable.
Require Import Data.Functor.
Require Import Data.Traversable.
Require Import GHC.Base.
Require Import GHC.Enum.
Require Import GHC.Num.
Require Import GHC.Real.
Require Control.Concurrent.Async.
Require BL.
Require IO.
Require Types.
Require Import Monads.

(* No type declarations to convert. *)

(* Midamble *)

Axiom show : Int -> String.

(* Converted value declarations: *)

Definition countBytes : BL.ByteString -> Types.Counts :=
  BL.foldl' (fun acc next => acc <<>> Types.countChar next) mempty.

Definition Foo@{i j k} : Type@{i} := Type@{j} -> Type@{k}.

Set Printing Universes.
Polymorphic Instance Foldable__eta (F : Type -> Type)
            `{Foldable F} : Foldable (fun (A : Type) => F A).
(** An alternative definition replaces (fun A => F A) with F, but that
    would impose the constraint that a = t1, which we do not want. *)
intros r k. apply k, H.
intros FF. destruct FF.
constructor.
- assumption.
- intros. exact (foldMap__ m a H0 H1 X X0).
- intros. exact (foldl__ b a X X0 X1).
- intros. exact (foldl'__ b a X X0 X1).
- intros. exact (foldr__ a b X X0 X1).
- intros. exact (foldr'__ a b X X0 X1).
- intros. exact (length__ a X).
- intros. exact (null__ a X).
- exact product__.
- exact sum__.
- intros. exact (toList__ a X).
Show Universes. (* a <= t1 *)
Defined.


Set Printing Universes.
Definition filesplit
  : list String -> IO.IO (list (String * Types.Counts)%type).
  intros paths. refine (@for_ list IO.IO _ _ _ _ _ _ _ paths _).
  intros fp. refine (IO.openFd fp IO.ReadOnly None IO.defaultFileFlags >>= _).
  intros fd. refine (((fromIntegral ∘ IO.fileSize) <$> IO.getFileStatus fp) >>= (fun (size: Int) => _)).
  Locate ">>".
  refine (IO.putStrLn (GHC.Base.hs_string__ "Using available cores: " <<>>
                                            show IO.numCapabilities) >> _).
  refine (let chunkSize := div size IO.numCapabilities in _).
  refine (_ >>= _).
  - Locate op_zlzdznzg__.
    refine (fold <$!> (@Control.Concurrent.Async.forConcurrently list _ _ _ _ _ _ _)).
    + 
      pose (@Foldable__beta list Foldable__list).
      red. red in f. intros r k.
      specialize (f r).
      assert (k' : Foldable__Dict (fun A : Type => list A) -> r).
      { admit. }
      Show Universes.
      specialize (f k').
      pose (f r). k).
      specialize (f r).
      intros r k. apply k, Foldable__list.
      intros FF. destruct FF.
      constructor.
      * assumption.
      * intros. exact (foldMap__ m a H H0 X X0).
      * intros. exact (foldl__ b a X X0 X1).
      * intros. exact (foldl'__ b a X X0 X1).
      * intros. exact (foldr__ a b X X0 X1).
      * intros. exact (foldr'__ a b X X0 X1).
      * intros. exact (length__ a X).
      * intros. exact (null__ a X).
      * exact product__.
      * exact sum__.
      * intros. exact (toList__ a X).
    +


      apply Foldable__beta.
    + pose (@Functor__beta list Functor__list).
      pose (@Foldable__beta list Foldable__list).
      pose (@Traversable__beta list Functor__list Foldable__list Traversable__list f f0).
      pose (t Async.Concurrently).
      intros r k. apply k, t.
      intros TD. destruct TD. constructor.
      * intros.
        Show Universes.
        apply (mapM__ m).

      
      Show Universes.
      
      exact t.
      apply (@Traversable__beta list _ _ Traversable__list _ _).
    Focus 2.
    + exact (enumFromTo (fromInteger 0) (IO.numCapabilities - fromInteger 1)).
    + exact (@Traversable__beta list _ _ Traversable__list _ _).
      * exact Traversable__list.
      * Set Typeclasses Debug. typeclasses eauto. 
      * typeclasses eauto.
      * 
    + 
    +
    refine (fold <$!> (Control.Concurrent.Async.forConcurrently
                         (enumFromTo (fromInteger 0) (IO.numCapabilities - fromInteger 1)) _)).
    
    +
    + Print Universes.
      exact Foldable__list.
    Focus 3.
    apply enumFromTo.
  - refine (fun result => IO.closeFd fd $> pair fp result).
  - Show Universes.
    refine (fold <$!> (Control.Concurrent.Async.forConcurrently (enumFromTo (fromInteger 0)
                                                                       (IO.numCapabilities - fromInteger 1)) _)).
                                                           _)) >>= _)).

  :=
  fun paths =>
    for_ paths (fun fp =>
                  IO.openFd fp IO.ReadOnly None IO.defaultFileFlags >>=
                  (fun fd =>
                     ((fromIntegral ∘ IO.fileSize) <$> IO.getFileStatus fp) >>=
                     (fun size =>
                        IO.putStrLn (GHC.Base.hs_string__ "Using available cores: " <<>>
                                     show IO.numCapabilities) >>
                        (let chunkSize := div size IO.numCapabilities in
                         (fold <$!>
                          (Control.Concurrent.Async.forConcurrently (enumFromTo (fromInteger 0)
                                                                                (IO.numCapabilities - fromInteger 1))
                           (fun n =>
                              let readAmount :=
                                fromIntegral (if n == (IO.numCapabilities - fromInteger 1) : bool
                                              then size - (n * chunkSize)
                                              else chunkSize) in
                              let offset := fromIntegral (n * chunkSize) in
                              countBytes <$!> BL.fdPRead fd readAmount offset))) >>=
                         (fun result => IO.closeFd fd $> pair fp result))))).

(* External variables:
     None String bool div enumFromTo fold for_ fromInteger fromIntegral list mempty
     op_z2218U__ op_zdzg__ op_zeze__ op_zgzg__ op_zgzgze__ op_zlzdzg__ op_zlzdznzg__
     op_zlzlzgzg__ op_zm__ op_zt__ pair show BL.ByteString BL.fdPRead BL.foldl'
     Control.Concurrent.Async.forConcurrently IO.IO IO.ReadOnly IO.closeFd
     IO.defaultFileFlags IO.fileSize IO.getFileStatus IO.numCapabilities IO.openFd
     IO.putStrLn Types.Counts Types.countChar
*)
