module RList

import Data.Fin

%default total

||| Random-access list based on a representation of binary numbers.
||| @ n the length of the list
||| @ a the type of elements
-- Based on the definition in de Caml given by Hongwei Xi
-- in the paper "Dependently Typed Data Structures"
data RList : (n : Nat) -> (a : Type) -> Type where
    ||| Empty list
    Nil : RList Z a
    ||| Singleton list
    One : a -> RList (S Z) a
    ||| List with an even number of elements, consisting of 
    ||| two equal-length lists of at least one element
    Even : RList (S n) a -> RList (S n) a -> RList (S (S (n + n))) a
    ||| List with an odd number of elements, consisting of 
    ||| two equal-length lists of at least one element,
    ||| and a single additional element
    Odd :  a -> RList (S n) a -> RList (S n) a -> RList (S (S (S (n + n)))) a

%name RList xs,ys,zs,ws

||| Append one element to the front of the list
(::) : a -> RList n a -> RList (S n) a
(::) {n = _} x [] = One x
(::) {n = _} x (One y) = Even (One x) (One y)
(::) {n = _} x (Even xs ys) = Odd x xs ys
(::) {n = (S (S (S (k + k))))} x (Odd y xs ys) = 
    rewrite plusSuccRightSucc k k in Even (x :: xs) (y :: ys)

||| Decompose the list into a pair consisting of the first element
||| and the rest of the list
uncons : RList (S n) a -> (a, RList n a)
uncons {n = _} (One x) = (x, [])
uncons {n = _} (Odd x xs ys) = (x, Even xs ys)
uncons {n = (S (k + k))} (Even xs ys) with (k)
  uncons {n = (S (k + k))} (Even (One x) ys) | Z = (x, ys)
  uncons {n = (S (k + k))} (Even xs ys) | (S j) = 
    let (x, xs) = uncons xs in let (y, ys) = uncons ys in
        rewrite sym $ plusSuccRightSucc j j in (x, Odd y xs ys)
        
||| The first element of the list
head : RList (S n) a -> a
head (One x) = x
head (Even xs _) = head xs
head (Odd x _ _) = x

||| All but the first element of the list
tail : RList (S n) a -> RList n a
tail = snd . uncons

||| The length of the list, provably equal to the type argument
length : RList n a -> Nat
length [] = 0
length (One _) = 1
length (Even xs ys) = length xs + length ys
length (Odd _ xs ys) = S (length xs + length ys)

private
verifyLen : (xs : RList n a) -> length xs = n
verifyLen {n = _} [] = Refl
verifyLen {n = _} (One _) = Refl
verifyLen {n = (S (S (k + k)))} (Even xs ys) = 
    rewrite verifyLen xs in 
    rewrite verifyLen ys in 
    rewrite plusSuccRightSucc k k in Refl
verifyLen {n = (S (S (S (k + k))))} (Odd _ xs ys) = 
    rewrite verifyLen xs in 
    rewrite verifyLen ys in 
    rewrite plusSuccRightSucc k k in Refl

||| Divide a Fin in half, rounding down, also halving the bounds
halfFin : Fin (n + n) -> Fin n
halfFin {n = Z} x = x
halfFin {n = (S Z)} x = FZ
halfFin {n = (S (S k))} FZ = FZ
halfFin {n = (S (S k))} (FS FZ) = FZ
halfFin {n = (S (S k))} (FS (FS x)) = 
    let x = replace (sym (plusSuccRightSucc k (S k))) x in FS (halfFin x)

||| Is this Fin even
evenFin : Fin n -> Bool
evenFin FZ = True
evenFin (FS x) = not (evenFin x)

||| The ith element of the list
lookup : (i : Fin n) -> RList n a -> a
lookup {n = _} i [] = absurd i
lookup {n = _} _ (One x) = x
lookup {n = (S (S (k + k)))} i (Even xs ys) = 
    let i = replace {P=Fin . S} (plusSuccRightSucc k k) i in 
        lookup (halfFin i) (assert_smaller (Even xs ys) (if evenFin i then xs else ys))
lookup {n = (S (S (S (k + k))))} FZ (Odd x _ _) = x
lookup {n = (S (S (S (k + k))))} (FS i) (Odd x xs ys) = 
    let i = replace {P=Fin . S} (plusSuccRightSucc k k) i in 
        lookup (halfFin i) (assert_smaller (Odd x xs ys) (if evenFin i then xs else ys))

||| Construct a random-access list from a list
fromList : (xs : List a) -> RList (length xs) a 
fromList [] = []
fromList (x :: xs) = x :: fromList xs