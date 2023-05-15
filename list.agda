{-# OPTIONS --allow-unsolved-metas #-}
module List where

open import BuiltIn

data List (E : Set) : Set where
  []   : List E 
  _::_ : E → List E → List E
infixr 5 _::_

length : {E : Set} → List E → Nat
length [] = 0
length (e :: es) = 1 + length es

tail : {E : Set} → List E → List E
tail (e :: es) = es
tail [] = []

head : {E : Set} → (list : List E) → (length list ≡ 0 → ⊥) → E
head [] lengthNotZero = absurd (lengthNotZero refl)
head (e :: es) _ = e

concat : {E : Set} → List E → List E → List E
concat (e :: es) rest = e :: (concat es rest) 
concat []             = id

concatNil : {E : Set} → (list : List E) → concat [] list ≡ list
concatNil _ = refl

listNotNil : {E : Set} (e : E) → (list : List E) → [] ≡ (e :: list) → ⊥
listNotNil _ _ ()

listNotLengthZero : {E : Set} (e : E) → (list : List E) → 0 ≡ length (e :: list) → ⊥
listNotLengthZero _ _ ()

concatNotNil : {E : Set} (list : List E) → (e : E) → (rest : List E) → [] ≡ (concat list (e :: rest)) → ⊥
concatNotNil []        e rest = listNotNil e rest
concatNotNil (l :: ls) e rest = listNotNil l (concat ls (e :: rest))

range : Nat → List Nat
range (suc n) = suc n :: range n
range 0       = 0 :: []

listMap : {A B : Set} → (A → B) → List A → List B
listMap f (l :: ls) = f l :: listMap f ls
listMap _ _         = []

isIn : (E : Set) → E → List E → Set
isIn E e list = Σ (List E) (λ fr → Σ (List E) (λ bk → (list ≡ concat fr (e :: bk))))

notInNil : {A : Set} → (a : A) → isIn A a [] → ⊥
notInNil a inNil = concatNotNil (car inNil) a (car (cdr inNil)) (cdr (cdr inNil))

singletonIsItself : {A : Set} → (a b : A) → isIn A a (b :: []) → a ≡ b
singletonIsItself a b inBList = {!!}

notHeadThenInRest : {A : Set} {list : List A} → (a b : A) → (isIn A a (b :: list) × (a ≡ b -> ⊥)) → isIn A a list
notHeadThenInRest a b (inBList ^ aNotb) = {!!}
