module STLC where

-- definition of lambda term syntax

data Nat = O | S Nat deriving (Eq, Ord, Show)

type Id = Nat 

data Ty = Var Id | Arr Ty Ty | Con deriving (Eq, Ord, Show)
          
data Term =
   Var_t Id
 | App_t Term Term
 | Lam_t Id Term
 | Const_t
 deriving (Eq, Ord, Show)  


-- definition of constraints

type Constr = (Ty,Ty)

type Constraints = [Constr]

occurs_dec :: Id -> Ty -> Bool
occurs_dec v (Var v') = v == v'
occurs_dec v (Arr t t') = occurs_dec v t || occurs_dec v t'
occurs_dec v Con = False

sub :: Ty -> Id -> Ty -> Ty
sub t v (Var v') = if v == v' then t else (Var v')
sub t v Con = Con
sub t v (Arr t1 t1') = Arr (sub t v t1) (sub t v t1')

type Substitution = [(Id,Ty)]

apply_subst :: Substitution -> Ty -> Ty
apply_subst s t = foldr (\(i,t') ac -> sub t' i ac) t s

apply_subst_constraint :: Substitution -> Constraints -> Constraints
apply_subst_constraint s cs = map (\(t,t') -> (apply_subst s t, apply_subst s t')) cs

-- unification

unify :: Constraints -> Maybe Substitution
unify [] = Just []
unify ((Con,Con) : cs) = unify cs
unify ((Var v, t) : cs) = if occurs_dec v t then Nothing
                            else maybe Nothing (\xs -> Just $ xs ++ [(v , t)]) (unify cs')
                           where
                             cs' = apply_subst_constraint [(v,t)] cs
unify ((t, Var v) : cs) = if occurs_dec v t then Nothing
                            else maybe Nothing (\xs -> Just $ xs ++ [(v , t)]) (unify cs')
                           where
                             cs' = apply_subst_constraint [(v,t)] cs
unify ((Arr l r, Arr l' r'):cs) = unify ((l,l') : (r,r') : cs)
unify _ = Nothing

-- typing contexts

type Tyctx = [(Id,Ty)]

-- Tc monad

data TcState = TcState {
                 next :: Id
               , constrs :: Constraints
               }

newtype TcM a = TcM { runTcM :: TcState -> (TcState, Maybe a) }

instance Functor TcM where
  fmap f m = TcM (\s ->
                   let
                     (s,t) = runTcM m s
                   in maybe (s, Nothing) (\x -> (s, Just (f x))) t)

instance Applicative TcM where
  pure x = TcM (\s -> (s, Just x))
  (TcM f) <*> m = undefined

instance Monad TcM where
  return x = TcM (\s -> (s,Just x))
  fail _ = TcM (\s -> (s, Nothing))
  (TcM m) >>= f = TcM (\s ->
                        let
                          (s',r) = m s
                        in case r of
                             Nothing -> (s', Nothing)
                             Just t -> runTcM (f t) s')

put :: TcState -> TcM ()
put s = TcM (\_ -> (s, Just ()))

get :: TcM TcState
get = TcM (\s -> (s, Just s))

modify :: (TcState -> TcState) -> TcM ()
modify f = get >>= \s -> put (f s)

fresh :: TcM Ty
fresh = do
  s <- get
  put (s{next = S (next s)})
  return (Var (next s))

add_constr :: Ty -> Ty -> TcM ()
add_constr t t'= modify (\s -> s{constrs = (t,t') : (constrs s)})

look :: Id -> Tyctx -> TcM Ty
look v [] = fail "Undefined value"
look v ((v',t) : ctx)
  = if v == v' then return t
      else look v ctx

                                  
gen_constr' :: Tyctx -> Term -> TcM Ty
gen_constr' ctx Const_t = return Con
gen_constr' ctx (Var_t v) = look v ctx
gen_constr' ctx (Lam_t v t)
  = do
      v' <- fresh
      t' <- gen_constr' ((v,v') : ctx) t
      return (Arr v' t')
gen_constr' ctx (App_t l r)
  = do
      t <- gen_constr' ctx l
      t' <- gen_constr' ctx r
      v <- fresh
      add_constr t (Arr t' v)
      return v

gen_constr :: Tyctx -> Term -> (Constraints, Maybe Ty)
gen_constr ctx e = (constrs tc, t)
  where
    r = runTcM (gen_constr' ctx e) (TcState O [])
    t = snd r
    tc = fst r


type_infer :: Term -> Maybe Ty
type_infer e
  = let (c,x) = gen_constr [] e
        r = unify c
     in case (r,x) of
           (Just s, Just t) -> Just (apply_subst s t)
           _ -> Nothing
  
