module Expression where

open import Data.Bool
open import Data.Product
open import Data.List
open import Data.String hiding (_++_)
open import Data.String.Unsafe

open import Function

Name : Set
Name = String

data Expr : Set where
    var : Name → Expr
    λ₁ : Name → Expr → Expr
    λ₂ : Name → Expr → Expr
    _$ₗ_ : Expr → Expr → Expr
    _$ᵣ_ : Expr → Expr → Expr
    _·_ : Expr → Expr → Expr
    Let : Expr → Name × Name → Expr → Expr

freeVariables :
    Expr → List Name
freeVariables (var x) =
    [ x ]
freeVariables (λ₁ x expr) =
    boolFilter (not ∘ (_==_ x)) (freeVariables expr)
freeVariables (λ₂ x expr) =
    boolFilter (not ∘ (_==_ x)) (freeVariables expr)
freeVariables (expr $ₗ expr₁) =
    (freeVariables expr) ++ (freeVariables expr₁)
freeVariables (expr $ᵣ expr₁) =
    (freeVariables expr) ++ (freeVariables expr₁)
freeVariables (expr · expr₁) =
    (freeVariables expr) ++ (freeVariables expr₁)
freeVariables (Let expr (x , y) expr₁) =
    (freeVariables expr) ++ boolFilter (not ∘ λ x₁ → (x₁ == x) ∧ (x₁ == y)) (freeVariables expr₁)

_[_:=_] : Expr → Name → Expr → Expr
(var x₁) [ x := N ] =
    case (x == x₁) of
         λ { true → N
           ; false → var x₁
           }
(λ₁ x₁ expr) [ x := N ] = {!!}
(λ₂ x₁ expr) [ x := N ] = {!!}
(expr $ₗ expr₁) [ x := N ] =
    (expr [ x := N ]) $ₗ (expr₁ [ x := N ])
(expr $ᵣ expr₁) [ x := N ] =
    (expr [ x := N ]) $ᵣ (expr₁ [ x := N ])
(expr · expr₁) [ x := N ] =
    (expr [ x := N ]) · (expr₁ [ x := N ])
(Let expr x₁ expr₁) [ x := N ] =
    {!!}
