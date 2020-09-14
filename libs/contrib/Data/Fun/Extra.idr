module Data.Fun.Extra

import Data.Fun
import Data.Rel
import Data.HVect

%default total

||| Apply an n-ary function to an n-ary tuple of inputs
public export
uncurry : {0 n : Nat} -> {0 ts : Vect n Type} -> Fun ts cod -> HVect ts -> cod
uncurry f [] = f
uncurry f (x::xs) = uncurry (f x) xs

||| Apply an n-ary function to an n-ary tuple of inputs
public export
curry : {n : Nat} -> {0 ts : Vect n Type} -> (HVect ts -> cod) -> Fun ts cod 
curry {ts = []    } f = f []
curry {ts = _ :: _} f = \x => curry (\xs => f (x :: xs))

{- 

The higher kind Type -> Type has a monoid structure given by
composition and the identity (Cayley). The type (n : Nat ** Vect n a)
has a monoid structure given by `(n, rs) * (m, ss) := (n + m, rs +
ss)` and `(0,[])`. 

  `Fun' : (n : Nat ** Vect n Type) -> Type -> Type` 
  
is then a monoid homomorphism between them. I guess this is some
instance of Cayley's theorem, but because of extensionality we can't
show we have an isomorphism.
-}
public export
homoFunNeut_ext : Fun [] cod -> id cod
homoFunNeut_ext x = x

public export
homoFunMult_ext : {n : Nat} -> {0 rs : Vect n Type} -> Fun (rs ++ ss) cod -> (Fun rs . Fun ss) cod
homoFunMult_ext {rs = []     }  gs = gs
homoFunMult_ext {rs = t :: ts} fgs = \x => homoFunMult_ext (fgs x)

public export
homoFunNeut_inv : id cod -> Fun [] cod
homoFunNeut_inv x = x

public export
homoFunMult_inv : {n : Nat} -> {0 rs : Vect n Type} -> (Fun rs . Fun ss) cod -> Fun (rs ++ ss) cod
homoFunMult_inv {rs = []     } gs = gs
homoFunMult_inv {rs = t :: ts} fgs = \x => homoFunMult_inv (fgs x)


||| Apply an n-ary function to an n-ary tuple of inputs
public export
applyPartially : {n : Nat} -> {0 ts : Vect n Type} 
               -> Fun (ts ++ ss) cod -> (HVect ts -> Fun ss cod)
applyPartially fgs = uncurry {ts} {cod = Fun ss cod} (homoFunMult_ext {rs=ts} {ss} fgs)


{- -------- (slightly) dependent versions of the above ---------------
   As usual, type dependencies make everything complicated          -}

||| Apply an n-ary dependent function to its tuple of inputs (given by an HVect)
public export
uncurryAll : {0 n : Nat} -> {0 ts : Vect n Type} -> {0 cod : Fun ts Type} 
        -> All ts cod -> (xs : HVect ts) -> uncurry cod xs
uncurryAll f [] = f
uncurryAll {ts = t :: ts} f (x :: xs) = uncurryAll {cod= cod x} (f x) xs

public export
curryAll : {n : Nat} -> {0 ts : Vect n Type} -> {0 cod : Fun ts Type}
        -> ((xs : HVect ts) -> uncurry cod xs)
        -> All ts cod
curryAll {ts = []     } f = f []
curryAll {ts = t :: ts} f = \x => curryAll (\ xs => f (x:: xs))

chainGenUncurried : {n : Nat} -> {0 ts : Vect n Type} -> {0 cod,cod' : Fun ts Type} -> 
           ((xs : HVect ts) -> uncurry cod xs -> uncurry cod' xs) ->  
           All ts cod -> All ts cod'
chainGenUncurried {ts = []} f gs = f [] gs
chainGenUncurried {ts = (t :: ts)} f gs = \x => chainGenUncurried (\u => f (x :: u)) (gs x)

public export
homoAllNeut_ext : Fun [] cod -> id cod
homoAllNeut_ext x = x

-- Not sure it's worth it getting the rest of Cayley's theorem to work

public export
extractWitness : {n : Nat} -> {0 ts : Vect n Type} -> {0 r : Rel ts} -> Ex ts r -> HVect ts
extractWitness {ts = []     }  _       = []
extractWitness {ts = t :: ts} (w ** f) = w :: extractWitness f

public export
extractWitnessCorrect : {n : Nat} -> {0 ts : Vect n Type} -> {0 r : Rel ts} -> (f : Ex ts r) -> 
                        uncurry {ts} r (extractWitness {r} f)
extractWitnessCorrect {ts = []     } f = f
extractWitnessCorrect {ts = t :: ts} (w ** f) = extractWitnessCorrect f

public export
introduceWitness : {0 r : Rel ts} -> (witness : HVect ts) -> 
                   uncurry {ts} r witness -> Ex ts r
introduceWitness []             f = f
introduceWitness (w :: witness) f = (w ** introduceWitness witness f)
