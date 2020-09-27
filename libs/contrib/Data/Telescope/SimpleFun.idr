||| N-ary simple (non-dependent) functions using telescopes
|||
||| Compare with `base/Data.Fun` and `contrib/Data.Fun.Extra` and with:
||| Guillaume Allais. 2019. Generic level polymorphic n-ary functions. TyDe 2019.
module Data.Telescope.SimpleFun

import Data.Telescope.Telescope
import Data.Telescope.Segment

||| An n-ary function whose codomain does not depend on its
||| arguments. The arguments may have dependencies.
public export
SimpleFun : (env : Environment gamma) -> {n : Nat} -> (0 delta : Segment n gamma) 
         -> (cod : Type) -> Type
SimpleFun env {n = 0  } [] cod = cod
SimpleFun env {n = S n} (ty :: delta) cod = (x : ty env) -> SimpleFun (env =. x) delta cod

public export
target : {0 env : Environment gamma} -> {0 delta : Segment n gamma} -> {cod : Type} 
      -> SimpleFun env delta cod -> Type
target {cod} _ = cod

public export
uncurry : {0 n : Nat} -> {0 env : Environment gamma} -> {0 delta : Segment n gamma} 
       -> (f : SimpleFun env delta cod) -> Environment env delta -> cod
uncurry f Empty     = f
uncurry f (x .= xs) = uncurry (f x) xs

public export
curry : {n : Nat} -> {0 env : Environment gamma} -> {0 delta : Segment n gamma}
     -> (f : Environment env delta -> cod)
     -> SimpleFun env delta cod
curry {n = 0  } {delta = []         } f = f Empty
curry {n = S n} {delta = ty :: delta} f = \x => curry (\xs => f (x .= xs))


