/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

/-!
# Lawful version of `MonadFunctor`

This file defines the `LawfulMonadFunctor` class, which adds laws to the `MonadFunctor` class.
These laws ensure that functor operations behave consistently and preserve monad laws.

-/

@[expose] public section

universe u v w

class LawfulMonadFunctor (m : semiOutParam (Type u → Type v)) (n : Type u → Type w)
    [Monad m] [Monad n] [MonadFunctor m n] : Prop where
  /-- Monad map preserves identity -/
  monadMap_id {α : Type u} :
    MonadFunctor.monadMap (fun {β} => (id : m β → _)) = (id : n α → _)

  /-- Monad map preserves composition -/
  monadMap_comp {α : Type u} (f : {β : Type u} → m β → m β) (g : {γ : Type u} → m γ → m γ) :
    (@MonadFunctor.monadMap m n _ α f) ∘ (@MonadFunctor.monadMap m n _ α g) =
      @MonadFunctor.monadMap m n _ α (f ∘ g)

class LawfulMonadFunctorT (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadFunctorT m n] : Prop where
  /-- Monad map preserves identity -/
  monadMap_id {α : Type u} :
    monadMap (fun {β} => (id : m β → _)) = (id : n α → _)

  /-- Monad map preserves composition -/
  monadMap_comp {α : Type u} (f : {β : Type u} → m β → m β) (g : {γ : Type u} → m γ → m γ) :
    (@monadMap m n _ α f) ∘ (@monadMap m n _ α g) = @monadMap m n _ α (f ∘ g)

export LawfulMonadFunctorT (monadMap_id monadMap_comp)

attribute [simp] monadMap_id monadMap_comp

instance {m n o} [Monad m] [Monad n] [Monad o] [MonadFunctor n o] [MonadFunctorT m n]
    [LawfulMonadFunctor n o] [LawfulMonadFunctorT m n] : LawfulMonadFunctorT m o where
  monadMap_id := by
    intro α
    let F : {β : Type _} → n β → n β :=
      fun {β} => @monadMap m n _ β (fun {γ} => (id : m γ → m γ))
    let IdN : {β : Type _} → n β → n β := fun {β} => (id : n β → n β)
    have hF : @F = @IdN := by
      funext β x
      exact congrFun (LawfulMonadFunctorT.monadMap_id (m := m) (n := n) (α := β)) x
    funext x
    change MonadFunctor.monadMap (m := n) F x = x
    rw [hF]
    exact congrFun (LawfulMonadFunctor.monadMap_id (m := n) (n := o) (α := α)) x
  monadMap_comp := by
    intro α f g
    let F : {β : Type _} → n β → n β := fun {β} => @monadMap m n _ β f
    let G : {β : Type _} → n β → n β := fun {β} => @monadMap m n _ β g
    let FG : {β : Type _} → n β → n β := fun {β} x => F (G x)
    let H : {β : Type _} → n β → n β := fun {β} => @monadMap m n _ β (f ∘ g)
    have hFG : @FG = @H := by
      funext β x
      exact congrFun (LawfulMonadFunctorT.monadMap_comp (m := m) (n := n) (α := β) f g) x
    funext x
    change MonadFunctor.monadMap (m := n) F (MonadFunctor.monadMap (m := n) G x) =
      MonadFunctor.monadMap (m := n) H x
    calc
      MonadFunctor.monadMap (m := n) F (MonadFunctor.monadMap (m := n) G x)
          = MonadFunctor.monadMap (m := n) FG x := by
              exact congrFun (LawfulMonadFunctor.monadMap_comp (m := n) (n := o) (α := α) F G) x
      _ = MonadFunctor.monadMap (m := n) H x := by
            rw [hFG]

instance lawfulMonadFunctorRefl {m} [Monad m] : LawfulMonadFunctorT m m where
  monadMap_id := by intro α; rfl
  monadMap_comp := by intro α f g; rfl

instance {m n} [MonadFunctor m n] : MonadFunctorT m n := inferInstance
