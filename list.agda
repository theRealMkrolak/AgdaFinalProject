{-# OPTIONS --allow-unsolved-metas #-}
module List where

open import BuiltIn

data List (E : Set) : Set where
  []   : List E
  _::_ : E → List E → List E
infixr 5 _::_

notNil : {E : Set} → (list : List E) → Set
notNil list = list ≡ [] → ⊥

length : {E : Set} → List E → Nat
length [] = 0
length (e :: es) = 1 + length es

tail : {E : Set} → List E → List E
tail [] = []
tail (e :: es) = es

head : {E : Set} → (list : List E) → notNil list → E
head [] notNil = absurd $ notNil refl
head (e :: es) _ = e

concat : {E : Set} → List E → List E → List E
concat []             = id
concat (e :: es) rest = e :: (concat es rest) 

nilConcat : {E : Set} → (list : List E) → concat [] list ≡ list
nilConcat _ = refl

listNotNil : {E : Set} {e : E} → (list : List E) → notNil (e :: list)
listNotNil _ ()

tailConcat=ConcatTail : {E : Set} → (xs ys : List E) → notNil xs → tail $ concat xs ys ≡ concat (tail xs) ys
tailConcat=ConcatTail []        ys xsNotNil = absurd $ xsNotNil refl
tailConcat=ConcatTail (x :: xs) _ _ = refl 

concatNotNil : {E : Set} → (list : List E) → (e : E) → (rest : List E) → notNil (concat list (e :: rest))
concatNotNil []        e rest = listNotNil rest
concatNotNil (x :: xs) e rest = listNotNil (concat xs (e :: rest))

range : Nat → List Nat
range 0       = 0 :: []
range (suc n) = suc n :: range n
-- range 5 = 5 :: 4 :: 3 :: 2 :: 1 :: 0 :: []

listMap : {A B : Set} → (A → B) → List A → List B
listMap f (x :: xs) = f x :: listMap f xs
listMap _ _         = []

isIn : (E : Set) → E → List E → Set
isIn E e list = Σ (List E) (λ fr → Σ (List E) (λ bk → (list ≡ concat fr (e :: bk))))
-- returns front and back of list such that when you insert e, you get back the list

notInNil : {A : Set} → (a : A) → isIn A a [] → ⊥
notInNil a inNil = concatNotNil (car inNil) a (car (cdr inNil)) (sym $ cdr (cdr inNil))

stupid : {A : Set} → (a b : A) → (as bs : List A) → a :: as ≡ b :: bs → a ≡ b
stupid a b as bs refl = refl

notHeadThenInRest : {A : Set} → (list : List A) → (a b : A) → (isIn A a (b :: list) × (a ≡ b → ⊥)) → isIn A a list
notHeadThenInRest list a b (inBList , aNotb) = tail frBList , (bkBList , trans (cong tail eq) tailConcatEq)
  where
    frBList = car inBList
    bkBList = car (cdr inBList)
    eq = cdr (cdr inBList)
    frBListNotNil = λ frBListNil → aNotb (sym $ stupid b a list bkBList (trans eq $ trans (cong (λ x → concat x (a :: bkBList)) frBListNil) (nilConcat (a :: bkBList))))
    tailConcatEq = tailConcat=ConcatTail frBList (a :: bkBList) frBListNotNil
-- if you know a is in a list, but it's not equal to the head, then it's in the tail                                                            

singletonIsItself : {A : Set} → (a b : A) → dec= A → isIn A a (b :: []) → a ≡ b
singletonIsItself a b decA inBList = cases (decA a b) id (λ a!=b → absurd $ notInNil a (notHeadThenInRest [] a b (inBList , a!=b)))
