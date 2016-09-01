module TypeInfer where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sumbool_rect :: (() -> a1) -> (() -> a1) -> Bool -> a1
sumbool_rect f f0 s =
  case s of {
   False -> f __;
   True -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Bool -> a1
sumbool_rec =
  sumbool_rect

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  acc_rect (\x0 _ x1 -> x x0 x1) a

well_founded_induction :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction =
  well_founded_induction_type

eq_dec :: Nat -> Nat -> Bool
eq_dec n =
  nat_rec (\m ->
    case m of {
     O -> False;
     S _ -> True}) (\_ iHn m ->
    case m of {
     O -> True;
     S m0 -> iHn m0}) n

type Id = Nat

eq_id_dec :: Id -> Id -> Bool
eq_id_dec =
  eq_dec

data Ty =
   Var Id
 | Arr Ty Ty
 | Con

ty_rect :: (Id -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> a1 -> Ty -> a1
ty_rect f f0 f1 t =
  case t of {
   Var i -> f i;
   Arr t0 t1 -> f0 t0 (ty_rect f f0 f1 t0) t1 (ty_rect f f0 f1 t1);
   Con -> f1}

ty_rec :: (Id -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> a1 -> Ty -> a1
ty_rec =
  ty_rect

eq_ty_dec :: Ty -> Ty -> Bool
eq_ty_dec t t' =
  ty_rec (\i t'0 ->
    case t'0 of {
     Var i0 -> sumbool_rec (\_ -> False) (\_ -> True) (eq_id_dec i i0);
     _ -> True}) (\_ h _ h0 t'0 ->
    case t'0 of {
     Arr t2 t3 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> False) (\_ -> True) (h0 t3)) (\_ -> True) (h t2);
     _ -> True}) (\t'0 ->
    case t'0 of {
     Con -> False;
     _ -> True}) t t'

type Constr = (,) Ty Ty

type List_constr = List Constr

type Varctxt = List Id

type Constraints = (,) Varctxt List_constr

mk_constraints :: Varctxt -> List_constr -> Constraints
mk_constraints c l =
  (,) c l

occurs_dec :: Id -> Ty -> Bool
occurs_dec v t =
  case t of {
   Var n -> eq_id_dec n v;
   Arr l r ->
    case occurs_dec v l of {
     False -> False;
     True -> occurs_dec v r};
   Con -> True}

sub :: Ty -> Id -> Ty -> Ty
sub t1 x t2 =
  case t2 of {
   Var n ->
    case eq_id_dec x n of {
     False -> t1;
     True -> Var n};
   Arr l r -> Arr (sub t1 x l) (sub t1 x r);
   Con -> Con}

remove :: Id -> Varctxt -> Varctxt
remove v ctx =
  case ctx of {
   Nil -> Nil;
   Cons y ys ->
    case eq_id_dec y v of {
     False -> remove v ys;
     True -> Cons y (remove v ys)}}

type Substitution = List ((,) Id Ty)

apply_subst :: Substitution -> Ty -> Ty
apply_subst s t =
  case s of {
   Nil -> t;
   Cons p s' ->
    case p of {
     (,) v t' -> apply_subst s' (sub t' v t)}}

apply_subst_constraint :: Substitution -> List_constr -> List_constr
apply_subst_constraint s l =
  case l of {
   Nil -> Nil;
   Cons c l' ->
    case c of {
     (,) t t1 -> Cons ((,) (apply_subst s t) (apply_subst s t1)) (apply_subst_constraint s l')}}

minus :: Varctxt -> (List Id) -> Varctxt
minus c xs =
  case xs of {
   Nil -> c;
   Cons x xs0 -> remove x (minus c xs0)}

type Unify_type = () -> Maybe Substitution

unify_body :: Constraints -> (Constraints -> () -> Unify_type) -> Maybe Substitution
unify_body l unify0 =
  case l of {
   (,) c l0 ->
    case l0 of {
     Nil -> Just Nil;
     Cons c0 l' ->
      case c0 of {
       (,) t t' ->
        case eq_ty_dec t t' of {
         False -> unify0 (mk_constraints c l') __ __;
         True ->
          case t of {
           Var v ->
            case occurs_dec v t' of {
             False -> Nothing;
             True ->
              case unify0
                     (mk_constraints (minus c (Cons v Nil))
                       (apply_subst_constraint (Cons ((,) v t') Nil) l')) __ __ of {
               Just s0 -> Just (Cons ((,) v t') s0);
               Nothing -> Nothing}};
           Arr l1 r ->
            case t' of {
             Var v ->
              case occurs_dec v t of {
               False -> Nothing;
               True ->
                case unify0
                       (mk_constraints (minus c (Cons v Nil))
                         (apply_subst_constraint (Cons ((,) v t) Nil) l')) __ __ of {
                 Just s0 -> Just (Cons ((,) v t) s0);
                 Nothing -> Nothing}};
             Arr l1' r' ->
              unify0 (mk_constraints c (Cons ((,) l1 l1') (Cons ((,) r r') l'))) __ __;
             Con -> Nothing};
           Con ->
            case t' of {
             Var v ->
              case occurs_dec v t of {
               False -> Nothing;
               True ->
                case unify0
                       (mk_constraints (minus c (Cons v Nil))
                         (apply_subst_constraint (Cons ((,) v t) Nil) l')) __ __ of {
                 Just s0 -> Just (Cons ((,) v t) s0);
                 Nothing -> Nothing}};
             _ -> Nothing}}}}}}

unify :: Constraints -> Maybe Substitution
unify l =
  well_founded_induction (\x x0 _ -> unify_body x x0) l __

data Term =
   Var_t Id
 | App_t Term Term
 | Lam_t Id Term
 | Const_t

type Tyctx = List ((,) Id Ty)

data Tc_state =
   MkState Id (List Id) (List ((,) Ty Ty))

type TcM a = Tc_state -> Maybe ((,) Tc_state a)

ret :: a1 -> TcM a1
ret x s =
  Just ((,) s x)

bind :: (TcM a1) -> (a1 -> TcM a2) -> TcM a2
bind c c' s =
  case c s of {
   Just p ->
    case p of {
     (,) s' v -> c' v s'};
   Nothing -> Nothing}

failT :: TcM a1
failT _ =
  Nothing

fresh :: TcM Ty
fresh s =
  case s of {
   MkState n ts cs -> Just ((,) (MkState (add (S O) n) (app ts (Cons n Nil)) cs) (Var n))}

add_constr :: Ty -> Ty -> TcM ()
add_constr t t' s =
  case s of {
   MkState n ts cs -> Just ((,) (MkState n ts (Cons ((,) t t') cs)) ())}

look :: Id -> Tyctx -> TcM Ty
look x g =
  case g of {
   Nil -> failT;
   Cons p g' ->
    case p of {
     (,) y t ->
      case eq_id_dec x y of {
       False -> ret t;
       True -> look x g'}}}

gen_constr :: Tyctx -> Term -> TcM Ty
gen_constr g t =
  case t of {
   Var_t v -> look v g;
   App_t l r ->
    bind (gen_constr g l) (\t1 ->
      bind (gen_constr g r) (\t2 ->
        bind fresh (\t0 -> bind (add_constr t1 (Arr t2 t0)) (\_ -> ret t0))));
   Lam_t v t0 ->
    bind fresh (\t1 -> bind (gen_constr (Cons ((,) v t1) g) t0) (\t2 -> ret (Arr t1 t2)));
   Const_t -> ret Con}

type_infer :: Term -> Maybe Ty
type_infer e =
  let {x = gen_constr Nil e (MkState O Nil Nil)} in
  case x of {
   Just p ->
    case p of {
     (,) t0 t ->
      case t0 of {
       MkState _ d cs ->
        case unify ((,) d cs) of {
         Just s0 -> Just (apply_subst s0 t);
         Nothing -> Nothing}}};
   Nothing -> Nothing}

