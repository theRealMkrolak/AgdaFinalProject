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

listNotNil : {E : Set} {e : E} → (list : List E) → [] ≡ (e :: list) → ⊥
listNotNil _ ()

listNotLengthZero : {E : Set} {e : E} → (list : List E) → length (e :: list) ≡ 0 → ⊥
listNotLengthZero _ ()

tailConcat=ConcatTail : {E : Set} (l1 l2 : List E) -> (l1 ≡  [] -> ⊥ ) -> (tail $ concat l1 l2) ≡ (concat (tail l1) l2)
tailConcat=ConcatTail []        l2 l1NeqNil = absurd (l1NeqNil $ refl)
tailConcat=ConcatTail (l :: l1) l2 l1NeqNil = refl 

concatNotNil : {E : Set} (list : List E) → (e : E) → (rest : List E) → [] ≡ (concat list (e :: rest)) → ⊥
concatNotNil []        e rest = listNotNil rest
concatNotNil (l :: ls) e rest = listNotNil (concat ls (e :: rest))

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

test : {A : Set} -> List A -> List A
test (a :: ls) = (a :: (a :: ls))
test [] = []

--fuck this function
stupid : {A : Set} -> (a : A) -> (l : List A) -> (b : A) -> (j : List A) -> ((a :: l) ≡ (b :: j)) -> (a ≡ b)
stupid a l b j refl = refl


notHeadThenInRest : {A : Set} (list : List A)  → (a b : A) → (isIn A a (b :: list) × (a ≡ b -> ⊥)) → isIn A a list
notHeadThenInRest list a b (inBList , aNotb) = let be = car inBList
                                                   cd = cdr inBList
                                                   en = car cd
                                                   eq = cdr cd
                                               in (tail be , (en ,
                                                             trans
                                                              (cong tail eq)
                                                              (tailConcat=ConcatTail
                                                                be
                                                                (a :: en)
                                                                (λ be=nil -> let list=a::en = trans eq $ trans (cong (λ x -> concat x (a :: en)) be=nil) (concatNil (a :: en))
                                                                in
                                                                aNotb (sym $ stupid b list a en list=a::en)))))

singletonIsItself : {A : Set} → (a b : A) → dec= A -> isIn A a (b :: []) → a ≡ b
singletonIsItself a b decA inBList = cases (decA a b) id (λ a!=b -> absurd $  notInNil a (notHeadThenInRest [] a b (inBList , a!=b)))


