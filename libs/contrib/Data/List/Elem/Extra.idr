module Data.List.Elem.Extra

import Data.List
import Data.List.Elem
import Data.DPair
import Data.Void

-- Auxiliary definitions for defining `unCons` below --

||| 'Postiive' evidence that a list is non-empty
data IsCons : List a -> Type where
  (::) : (x : a) -> (xs : List a) -> IsCons (x :: xs)

||| Turns the negative information proposition that the list is not
||| empty into positive evidence that it's not empty.
negativeToPositive : (xs : List a) -> Not (xs = []) -> IsCons xs
negativeToPositive [] f with (f Refl)
 negativeToPositive [] f | _ impossible
negativeToPositive (x :: xs) f = x :: xs

||| A positively non-empty list is a cons
unCons' : (0 xs : List a) -> (0 _ : IsCons xs)
      -> Exists {type = a} \x => Exists {type = List a} \xs' => xs = (x :: xs')
unCons' .(x :: xs) (x :: xs) = Evidence x $ Evidence xs Refl
-- ----------------------------------------------------

||| A non-empty list is a cons
export
unCons : (0 xs : List a) -> (0 _ : Not (xs = Nil))
      -> Exists {type = a} \x => Exists {type = List a} \xs' => xs = (x :: xs')
unCons xs prf = unCons' xs (negativeToPositive xs prf)

||| A list with an element is non-empty
export
elemNonEmpty : Elem x xs -> Not (xs = [])
elemNonEmpty Here _ impossible
elemNonEmpty (There pos) _ impossible

export
invertMap : (0 f : a -> b) -> Elem y (map f xs) -> Exists {type = a} \x => (Elem x xs, f x = y)
invertMap  {xs        } {y      } f  pos with (let observation : (xs = [] -> map f xs = []) =
                                                                 \Refl    => Refl
                                              in unCons xs
                                               $ contrapositive observation
                                               $ elemNonEmpty pos)
 invertMap {xs = x::xs} {y = f x} f  Here       | Evidence x $ Evidence xs Refl
   = Evidence x (Here, Refl)
 invertMap {xs = x::xs} {y      } f (There pos) | Evidence x $ Evidence xs Refl
   = let Evidence y (pos, pf) = invertMap f pos in
     Evidence y (There pos, pf)
