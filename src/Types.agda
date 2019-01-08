module Types where

open import Data.List
open import Data.Nat
open import Data.String hiding (_++_)

data TVar : Set where
    tyVar : String → TVar

data Type : Set where
    Atom : TVar → Type
    _⊗_ : Type → Type → Type
    _⇐_ : Type → Type → Type
    _⇒_ : Type → Type → Type

TVars : Type → List TVar
TVars (Atom x) = [ x ]
TVars (t ⊗ t₁) = TVars t ++ TVars t₁
TVars (t ⇐ t₁) = TVars t ++ TVars t₁
TVars (t ⇒ t₁) = TVars t ++ TVars t₁
