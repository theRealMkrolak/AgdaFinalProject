{-# OPTIONS --allow-unsolved-metas #-}
module List where

open import BuiltIn


data List (A : Set) : Set where
  nil : List A 
  ::  : A -> List A -> List A

nil!=::n : {E : Set} (n : E) -> (l : List E ) -> (nil ≡ (:: n l) -> ⊥)
nil!=::n n l ()

concat : {E : Set} -> List E -> List E -> List E
concat (:: el l) l2 = :: el (concat l l2) 
concat nil = id

concatNilL=L : {E : Set} -> (l : List E)  -> (concat nil l ≡ l)
concatNilL=L l = refl

range : Nat -> List Nat
range (suc n) = (:: (suc n) (range n))
range 0 = (:: 0 nil)

listMap : {A B : Set} → (A → B) → List A → List B
listMap f (:: l ls) = (:: (f l) (listMap f ls))
listMap _ _ = nil

isIn : (E : Set) → (e : E) → (l : List E) → Set
isIn E e l = Σ (List E) (λ fr → Σ (List E) (λ bk → (l ≡ (concat fr (:: e bk)))))

aIsNotInNil : {A : Set} -> (a : A) -> (isIn A a nil) -> ⊥
aIsNotInNil a aIsInNil = ?


aIsIn[b]a=b : {A : Set} -> (a b : A) -> (isIn A a (:: b nil)) -> (a ≡ b)
aIsIn[b]a=b a b isInAB = ?

aIsInbL&a!=b=>aIsInL : {A : Set} {l : List A} -> (a b : A)  -> (isIn A a (:: b l) × (a ≡ b -> ⊥)) -> (isIn A a l)
aIsInbL&a!=b=>aIsInL a b (aIn::bl ^ aNeqb) = {!!}



