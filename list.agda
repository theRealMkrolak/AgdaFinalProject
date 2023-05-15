{-# OPTIONS --allow-unsolved-metas #-}
module List where

open import BuiltIn


data List (A : Set) : Set where
  nil : List A 
  ::  : A -> List A -> List A


tail : {E : Set} -> List E -> List E
tail (:: el l) = l
tail nil = nil

concat : {E : Set} -> List E -> List E -> List E
concat (:: el l) l2 = :: el (concat l l2) 
concat nil = id

concatNilL=L : {E : Set} -> (l : List E)  -> (concat nil l ≡ l)
concatNilL=L l = refl

nil!=::n : {E : Set} (n : E) -> (l : List E ) -> (nil ≡ (:: n l) -> ⊥)
nil!=::n n l ()

nil!=concatLa::J : {E : Set} (l : List E) -> (e : E) -> (j : List E) -> (nil ≡ (concat l (:: e j)) -> ⊥)
nil!=concatLa::J nil       e j = nil!=::n e j
nil!=concatLa::J (:: ls l) e j = nil!=::n ls (concat l (:: e j))

range : Nat -> List Nat
range (suc n) = (:: (suc n) (range n))
range 0 = (:: 0 nil)

listMap : {A B : Set} → (A → B) → List A → List B
listMap f (:: l ls) = (:: (f l) (listMap f ls))
listMap _ _ = nil

isIn : (E : Set) → (e : E) → (l : List E) → Set
isIn E e l = Σ (List E) (λ fr → Σ (List E) (λ bk → (l ≡ (concat fr (:: e bk)))))

aIsNotInNil : {A : Set} -> (a : A) -> (isIn A a nil) -> ⊥
aIsNotInNil a aIsInNil =  (nil!=concatLa::J (car aIsInNil) a (car $ cdr aIsInNil))  $ (cdr (cdr aIsInNil))


aIsIn[b]a=b : {A : Set} -> (a b : A) -> (isIn A a (:: b nil)) -> (a ≡ b)
aIsIn[b]a=b a b (x , (y , prf)) = 
  begin
    {!a
  =⟨⟩
    ?!}

aIsInbL&a!=b=>aIsInL : {A : Set} {l : List A} -> (a b : A)  -> (isIn A a (:: b l) × (a ≡ b -> ⊥)) -> (isIn A a l)
aIsInbL&a!=b=>aIsInL a b (aIn::bl ^ aNeqb) = {!!}



