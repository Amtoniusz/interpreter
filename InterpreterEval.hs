module InterpreterEval where

import Data.Map (Map)
import Data.List 
import Data.Function
import qualified Data.Map as Map
import AbsGramatyka
import ErrM

data Result =    ResStr String 
                |ResInt Integer 
                |ResBool Bool
                |ReturnStr String 
                |ReturnInt Integer 
                |ReturnBool Bool
                |ReturnNono 
                |Error String 
                |ResRefStr Loc 
                |ResRefInt Loc
                |ResRefBool Loc
                |No
                deriving (Eq,Ord,Show)

type Loc = Integer

type Name = String


data PasArg = Pat Type | 
              Par Ref 
              deriving (Eq,Ord,Show)

data Id = IdVar Name 
         |IdFun Name [PasArg]
         |IdPrint
         deriving (Eq,Ord,Show)

data Data = DInt Integer 
           |DStr String
           |DBool Bool
           |DFun Type [Arg] Env Block
           |DList [String] 
           deriving (Eq,Ord,Show)

type Store = Map Loc Data

type Env = Map Id Loc


-- failure :: Show a => a -> Result
-- failure x = Bad $ "Undefined case: " ++ show x
addStore :: Store -> Loc -> Data -> Store
addStore store loc d = (Map.insert loc d store)

find_env :: Env -> Id -> Maybe Loc
find_env env id = case (Map.member id env) of
                                        True  -> Just (env Map.! id)
                                        False -> Nothing

find_store :: Store -> Loc -> Maybe Data 
find_store store loc = case (Map.member loc store) of
                                        True  -> Just (store Map.! loc)
                                        False -> Nothing

find_env_force :: Env -> Id -> Loc
find_env_force env id = case (find_env env id) of
                                        Just x -> x


find_data :: Store -> Env -> Id -> Maybe Data
find_data store env id =  case (find_env env id) of 
                                            Nothing -> Nothing
                                            Just loc -> (find_store store loc)

find_loc_data :: Store -> Env -> Id -> (Maybe Loc,Maybe Data)                                                                                  
find_loc_data store env id = (find_env env id, find_data store env id )


unwrap_Ident :: Ident -> Id
unwrap_Ident (Ident s) = (IdVar s)

eq_type_aux::Result -> Integer
eq_type_aux a = case a of
          ResStr x -> 0
          ResInt x -> 1
          ResBool x   -> 2
          Error x      -> 3
          ResRefStr x  -> 4 
          ResRefInt x -> 5 
          ResRefBool x -> 6
          ReturnStr x  -> 7
          ReturnInt x  -> 8
          ReturnBool x -> 9
          ReturnNono -> 10
          No -> 11 

unwrap_ResInt:: Result -> Integer
unwrap_ResInt (ResInt x) = x

eq_type :: Result -> Result -> Bool
eq_type a b =  (eq_type_aux a ) == (eq_type_aux b)

eval :: Exp -> Result
eval exp = case evalExp (Map.empty) (Map.empty) exp of
                                                (a,b,c) -> c
evalTestBlk :: Block -> Result
evalTestBlk blk = case evalBlk (Map.empty) (Map.empty) blk of
                                                (a,b,c) -> c

evalExp ::Store -> Env -> Exp -> (Store,Env,Result)
evalExp store env (EInt n)  = (store,env,(ResInt n))
evalExp store env ETrue     = (store,env,(ResBool True))
evalExp store env EFalse    = (store,env,(ResBool False))
evalExp store env (Not exp)   = case (evalExp store env exp) of (s,e,(Error err))    -> (store,env,(Error err))
                                                                (s,e,(ResBool b))  -> (store,env,(ResBool (not (b))))
                                                                (s,e,x)            ->(store,env,(Error ("Wrong type in Negation (!): expected bool and get: " ++ printRes(x)) ))

evalExp store env (Neg e)   = case (evalExp store env e) of (s,e,(Error err))   -> (store,env,(Error err))
                                                            (s,e,(ResInt n))  -> (store,env,(ResInt ((-1) * n)))
                                                            (s,e,x)             -> (store,env,(Error ("Wrong type in Negation (-): expected int and get: " ++ printRes(x)) ))

evalExp store env (EIdent (Ident s))  = case (find_data store env (unwrap_Ident (Ident s))) of 
                                                                              Just (DInt x)  -> (store,env,(ResInt x))   
                                                                              Just (DStr x)  -> (store,env,(ResStr x))   
                                                                              Just (DBool x) -> (store,env,(ResBool x)) 
                                                                              Nothing  -> (store,env,(Error ("Variable " ++ s ++ " wasn't defined")))

evalExp store env (ERef (Ident s)) = case (find_loc_data store env (unwrap_Ident (Ident s))) of 
                                                                              (Just loc, Just (DInt x))  -> (store,env,(ResRefInt loc))   
                                                                              (Just loc,Just (DStr x))  -> (store,env,(ResRefStr loc))   
                                                                              (Just loc,Just (DBool x)) -> (store,env,(ResRefBool loc))
                                                                              _ -> (store,env,(Error ("Variable " ++ s ++ " wasn't defined"))) 
evalExp store env (EStr string) = (store,env,(ResStr ( string)))

evalExp store env (EMul exp1 op exp2) = let (s,_,exp11) = evalExp store env exp1 in 
                                        let (s1,_,exp21) = evalExp s env exp2 in 
                                        case (exp11,exp21) of
                                                            (Error x, _)        -> (store,env,(Error x))
                                                            (ResStr x,_)        -> (store,env,(Error ("Wrong types for operator " ++ printMulop(op) ++ printRes(exp11) ++ printRes(exp21)) )) 
                                                            (ResBool x,_)       -> (store,env,(Error ("Wrong types for operator " ++ printMulop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
                                                            (ResInt x,ResInt 0) -> case op of 
                                                                                            Mod   -> (store,env,(Error "Mod by 0")) 
                                                                                            Div   -> (store,env,(Error "Divide by 0")) 
                                                                                            Times -> (s1,env,(ResInt 0)) 
                                                            (ResInt x,ResInt y) -> case op of 
                                                                                            Mod   -> (s1,env,(ResInt (mod x y)))
                                                                                            Div   -> (s1,env,(ResInt (div x y))) 
                                                                                            Times -> (s1,env,(ResInt (x*y)))
                                                            (ResInt x,_)        -> (store,env,(Error ("Wrong types for operator " ++ printMulop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
                                                            (_,_)               -> (store,env,(Error ("Wrong types for operator " ++ printMulop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
evalExp store env (EAdd exp1 op exp2) = let (s,_,exp11) = evalExp store env exp1 in 
                                        let (s1,_,exp21) = evalExp s env exp2 in 
                                        case (exp11,exp21) of
                                                            (Error x, _)        -> (store,env,(Error x))
                                                            (ResStr x,ResStr y) -> case op of
                                                                                            Plus  -> (s1,env,(ResStr (x ++ y))) 
                                                                                            Minus -> (store,env,(Error ("Wrong types for operator " ++ printAddop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
                                                            (ResStr x,_)        -> (store,env,(Error ("Wrong types for operator " ++ printAddop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
                                                            (ResBool x,_)       -> (store,env,(Error ("Wrong types for operator " ++ printAddop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
                                                            (ResInt x,ResInt y) -> case op of 
                                                                                            Plus  -> (s1,env,(ResInt (x + y))) 
                                                                                            Minus -> (s1,env,(ResInt (x - y)))
                                                            (ResInt x,_)        -> (store,env,(Error ("Wrong types for operator " ++ printAddop(op) ++ printRes(exp11) ++ printRes(exp21)) ))
                                                            (_,_)               -> (store,env,(Error ("Wrong types for operator " ++ printAddop(op) ++ printRes(exp11) ++ printRes(exp21)) ))                                                  

evalExp store env (ERel exp1 op exp2) = let (s,e,exp11) = evalExp store env exp1 in 
                                        let (s1,e1,exp21) = evalExp s e exp2 in 
                                        case (exp11,exp21) of
                                                            (Error x, _)        -> (store,env,(Error x))
                                                            (ResStr x,ResStr y) -> case op of
                                                                                            LTH -> (s1,e1,(ResBool (x < y)))
                                                                                            LE  -> (s1,e1,(ResBool (x <= y))) 
                                                                                            GTH -> (s1,e1,(ResBool (x > y)))
                                                                                            GE  -> (s1,e1,(ResBool (x >= y)))
                                                                                            EQU -> (s1,e1,(ResBool (x == y)))
                                                                                            NE  -> (s1,e1,(ResBool (x /= y))) 
                                                            (ResStr x,y)        -> (store,env,(Error ("Differents types: " ++ printRes exp11 ++ " and " ++ printRes exp21 )))
                                                            (ResBool x, ResBool y)-> case op of
                                                                                           LTH -> (s1,e1,(ResBool (x < y)))
                                                                                           LE  -> (s1,e1,(ResBool (x <= y))) 
                                                                                           GTH -> (s1,e1,(ResBool (x > y)))
                                                                                           GE  -> (s1,e1,(ResBool (x >= y)))
                                                                                           EQU -> (s1,e1,(ResBool (x == y)))
                                                                                           NE  -> (s1,e1,(ResBool (x /= y))) 
                                                            (ResBool x,_)       -> (store,env,Error ("Differents types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (ResInt x,ResInt y) -> case op of 
                                                                                            LTH -> (s1,e1,(ResBool (x < y)))
                                                                                            LE  -> (s1,e1,(ResBool (x <= y))) 
                                                                                            GTH -> (s1,e1,(ResBool (x > y)))
                                                                                            GE  -> (s1,e1,(ResBool (x >= y)))
                                                                                            EQU -> (s1,e1,(ResBool (x == y)))
                                                                                            NE  -> (s1,e1,(ResBool (x /= y)))
                                                            (ResInt x,_)        -> (store,env,Error ("Differents types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (_,_)               -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))                                                            

evalExp store env (EAnd exp1 exp2) = let (s,e,exp11) = evalExp store env exp1 in 
                                        let (s1,e1,exp21) = evalExp s e exp2 in 
                                        case (exp11,exp21) of
                                                            (Error x, _)        -> (store,env,(Error x))
                                                            (ResStr x,ResStr y) -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 )) 
                                                            (ResStr x,_)        -> (store,env,Error ("Differents types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (ResBool x, ResBool y)-> (s1,e1,(ResBool (x && y)))
                                                            (ResBool x,_)       -> (store,env,Error ("Differents types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (ResInt x,ResInt y) -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 )) 
                                                            (ResInt x,_)        -> (store,env,Error ("Differents types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (_,_)               -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))                                                            

evalExp store env (EOr exp1 exp2) = let (s,e,exp11) = evalExp store env exp1 in 
                                        let (s1,e1,exp21) = evalExp s e exp2 in 
                                        case (exp11,exp21) of
                                                            (Error x, _)        -> (store,env,(Error x))
                                                            (ResStr x,ResStr y) -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 )) 
                                                            (ResStr x,_)        -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (ResBool x, ResBool y)-> (s1,e1,(ResBool (x || y)))
                                                            (ResBool x,_)       -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (ResInt x,ResInt y) -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 )) 
                                                            (ResInt x,_)        -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))
                                                            (_,_)               -> (store,env,Error ("Wrong types: " ++ printRes exp11 ++ " and " ++ printRes exp21 ))                                                            

evalExp store env (EFun (Ident name) expList) = let (storeP, envP, res, resList) =  evalExpList store env expList in  
                                                  case res of (Error x) ->  (storeP, envP, res)
                                                              (_) ->  (let args =  map convertResToPasArg resList in
                                                                        let id =  IdFun name args in
                                                                          let (mloc, mdfun) = find_loc_data storeP envP id in 
                                                                            (case (mloc, mdfun) of (Nothing, _) ->  (storeP, envP, (Error ("function: " ++  name  ++ " not found"))) 
                                                                                                   ((Just loc), Nothing ) -> (storeP, envP, (Error ("function: " ++  name  ++ " not found"))) 
                                                                                                   ((Just loc), (Just dfun)) -> (callFunction storeP envP resList dfun))) 

convertResToData:: Result -> Data
convertResToData (ResInt x) = DInt x
convertResToData (ResBool x) = DBool x
convertResToData (ResStr x)  = DStr x

convertResToLoc:: Result -> Loc
convertResToLoc (ResRefStr loc) = loc 
convertResToLoc (ResRefInt loc) = loc
convertResToLoc (ResRefBool loc) = loc

loadArgument:: (Store,Env, Result) -> Result -> Arg -> (Store,Env, Result)
loadArgument (store,env,res) argV argT = case res  of 
                                                     (Error x) ->  (store,env,res)
                                                     (_) -> (if chackArg store env argT argV  == False then (store,env, Error "Worng type of argument")
                                                                                               else (case argT of (ArgType IntType (Ident name)) -> (alloc store env (IdVar name) (convertResToData argV))
                                                                                                                  (ArgType StrType (Ident name)) -> (alloc store env (IdVar name) (convertResToData argV))     
                                                                                                                  (ArgType BoolType (Ident name)) -> (alloc store env (IdVar name) (convertResToData argV))          
                                                                                                                  (ArgRef  IntRef  (Ident name)) -> (store,(Map.insert  (IdVar name) (convertResToLoc argV) env), No)
                                                                                                                  (ArgRef  StrRef  (Ident name)) -> (store,(Map.insert (IdVar name) (convertResToLoc argV) env), No)
                                                                                                                  (ArgRef  BoolRef  (Ident name)) -> (store,(Map.insert (IdVar name) (convertResToLoc argV) env), No)))

loadArguments:: (Store,Env,Result )-> [Result] -> [Arg] -> (Store,Env, Result)
loadArguments (store,env,res) [] [] = (store,env,res) 
loadArguments (store,env,res) (r:rs) [] = (store,env,Error "Wrong nr of arugments numbers")
loadArguments (store,env,res) [] (a:as) = (store,env,Error "Wrong nr of arugments numbers")
loadArguments (store,env,res) (r:rs) (a:as) =  (case res of 
                                                          (Error x) -> (store,env,res)
                                                          (_) -> let (s,e,ress) = (loadArgument (store,env,res) r a) in
                                                                      loadArguments (s,e,ress) rs as)


callFunction :: Store -> Env ->  [Result] -> Data  -> (Store, Env, Result)
callFunction store env args (DFun returnType argsTyps envF block) =  let (storeP, envP, res) =  loadArguments (store, envF, No) args argsTyps in  
                                                                     case res of (Error x) -> (storeP, envP, res) 
                                                                                 (_) -> (let (s,e,r) = (evalBlk storeP envP block) in
                                                                                          case  (returnType, r) of
                                                                                          (IntType, ReturnInt x ) -> (s,e, (ResInt x)) 
                                                                                          (StrType, ReturnStr x) -> (s,e,(ResStr x)) 
                                                                                          (BoolType, ReturnBool x) -> (s,e,(ResBool x)) 
                                                                                          (VoidType, ReturnNono) -> (s,e,(No))
                                                                                          (VoidType, No) -> (s,e,(No)) 
                                                                                          (x,y) -> (s,e,Error ("Wrong return type: expected:" ++ (printType x) ++ " get: " ++ (printRes y))))  

-- Statement

new_loc_aux:: Loc->Loc-> [Loc] -> Loc
new_loc_aux x1 x2 l = case l of []    -> if x1+1 < x2 then x1+1 else x2+1
                                (h:t) -> if x1+1 < x2 then x1+1 else (new_loc_aux x2 h t)
new_loc :: Store -> Loc
new_loc store = case (sort (Map.keys store)) of
                                      [] -> 0 
                                      [h] -> h+1 
                                      (h1:h2:t) -> new_loc_aux h1 h2 t 
 
-- allocEnv :: Env -> Id -> Env
-- allocEnv env id = (Map.insert  id (new_loc env) env )

-- allocLoc :: Env -> Id -> Loc -> Env
-- allocLoc env id loc = (Map.insert  id loc env )

-- allocStore :: Store -> Loc -> Data -> Store
-- allocStore store loc d = (Map.insert  loc d store)

alloc :: Store -> Env -> Id -> Data -> (Store,Env, Result)
alloc store env id d = let loc = new_loc store in
                        let envP = (Map.insert  id loc env ) in 
                          let storeP = (Map.insert loc d store) in 
                            (storeP, envP, No)

makeIdVar :: Ident -> Id
makeIdVar (Ident i) = (IdVar i)
 

--TODO reftype variable if needed
evalItem :: Store -> Env -> Type -> Item   -> (Store,Env,Result)
evalItem store env t (NoInit ident) = case t of
                                        IntType  -> (alloc store env (makeIdVar ident) (DInt 0))
                                        StrType  -> (alloc store env (makeIdVar ident) (DStr ""))
                                        BoolType -> (alloc store env (makeIdVar ident) (DBool False))
                                        x        -> (store, env, (Error ("Wrong type of declaration expected int, string or bool and get: " ++ printType  x))) 

evalItem store env t (Init ident exp) =let (storeP, envP, result) =   (evalExp store env exp) in
                                          case (result, t) of
                                            (Error x, _)           -> (store, env, result)
                                            (ResInt x, IntType)    -> (alloc storeP env (makeIdVar ident) (DInt x) ) 
                                            (ResStr x, StrType)    -> (alloc storeP env (makeIdVar ident) (DStr x))
                                            (ResBool x, BoolType)  -> (alloc storeP env (makeIdVar ident) (DBool x))
                                            (_, VoidType)          -> (store, env, (Error ("Wrong type of declaration expected int, string or bool and get: " ++ printType  t)))
                                            (_, _)                 -> (store, env, (Error ("Different types in declaration : "  ++  printRes result ++" and" ++ printType t )))


toStr :: Ident-> String
toStr (Ident s) = s

evalStm :: Store -> Env -> Stm -> (Store, Env,Result)
evalStm store env (Decl t items) = go  store env t items where
                                  go store env t [] = (store,env,No)
                                  go store env t (x:xs) = let (storeP, envP, result) =  evalItem store env t x in
                                                       case result of (Error e) ->  (store,env,(Error e)) 
                                                                      _         ->  go storeP envP t xs  


evalStm store env (Ass ident exp) = case (find_loc_data store env (makeIdVar ident)) of 
                                                                                        (Nothing, _) -> (store, env, (Error ("Variable"++ toStr(ident) ++ "doesn't exist")))
                                                                                        (Just loc, Nothing) -> (store, env, (Error ("Variable"++ toStr(ident) ++ "doesn't exist") ))  
                                                                                        (Just loc, Just d) -> let (storeP, envP, result) =  evalExp store env exp in
                                                                                                              case (result, d) of
                                                                                                                      (Error x,_)     -> (store, env, (Error x))
                                                                                                                      (ResInt x, DInt y)   -> (addStore storeP loc (DInt x), env, No )
                                                                                                                      (ResStr x, DStr y)   -> ((addStore storeP loc (DStr x)), env, No )
                                                                                                                      (ResBool x, DBool y) -> ((addStore storeP loc (DBool x)), env, No )
                                                                                                                      (_,_)           -> (store, env, Error ("Wrong type of assigment " ++ printRes result++ " and "  ++ printData d ))
                                                                                        
evalStm store env (Cond exp block) =  evalStm store env (CondElse exp block (Blk []))

evalStm store env (CondElse exp block1 block2) = let (storeP, envP, ret ) = evalExp store env exp in
                                                 case ret of (Error x)   -> (storeP, envP, ret )
                                                             (ResBool x) -> if x then evalBlk storeP envP block1 
                                                                                 else evalBlk storeP envP block2
                                                             (x)   -> (storeP, envP, Error ("Wrong type in condition if: expected bool get: " ++ printRes x) )

evalStm store env (While exp block) = let (storeP, envP, ret ) = evalExp store env exp in
                                          case ret of (Error x)   -> (storeP, envP, ret)
                                                      (ResBool x) -> if x then 
                                                                          (let (storeS, envS, retS ) = evalBlk storeP envP block in
                                                                          case retS of 
                                                                                      Error x -> (storeS, envS, retS )
                                                                                      ReturnBool x -> (storeS, envS, retS )
                                                                                      ReturnStr x -> (storeS, envS, retS )
                                                                                      ReturnInt x -> (storeS, envS, retS )
                                                                                      ReturnNono -> (storeS, envS, retS)
                                                                                      _       ->  (evalStm storeS envS (While exp block)) 
                                                                          )  
                                                                          else (storeP, envP, No)  
                                                      (x)   -> (storeP, envP, Error ("Wrong type in condition in while: expected Bool get: " ++ printRes x) ) 

evalStm store env (Print ex) =  evalStmPrintAux  (store, env, No) "" ex

evalStm store env (StmExp exp) =  let (storeP,_, ret) = evalExp store env exp in (storeP,env, ret)


evalStm store env (RetVal exp) = let (storeP,evalP, ret) = evalExp store env exp in 
                                 case ret of  (ResBool x) -> (storeP,evalP, ReturnBool x )
                                              (ResStr x) -> (storeP,evalP, ReturnStr x )
                                              (ResInt x) -> (storeP,evalP, ReturnInt x )
                                              (_) -> (storeP,evalP, Error ("Wrong return type:" ++ (printRes ret) ) )
    

evalStm store env Ret =  (store,env,ReturnNono)

--   DeclTop type_ items -> failure x
evalStm store env (FunDec fun)  = evalStm store env (FunDef fun (Blk []))

evalStm store env (FunDef (FunPref t (Ident name) args) block) = let fun = IdFun name (map convertArgToPasArg args)  in
                                                                  let loc = new_loc store in 
                                                                    let envP = Map.insert fun loc env in
                                                                      let dfun = (DFun t args envP block) in
                                                                        let storeP = Map.insert loc dfun store in
                                                                          (storeP, envP, No) 

convertResToRet :: Result -> Result
convertResToRet (ResBool x) = (ReturnBool x)
convertResToRet (ResStr x) = (ReturnStr x)
convertResToRet (ResInt x) = (ReturnInt x)

convertRetToRes :: Result -> Result
convertRetToRes (ReturnBool x) = (ResBool x)
convertRetToRes (ReturnStr x) = (ResStr x)
convertRetToRes (ReturnInt x) = (ResInt x)

evalExpListAux :: (Store,Env,Result,[Result]) -> Exp -> (Store,Env,Result,[Result])
evalExpListAux (store, env, res, l) exp = case res of (Error x) -> (store, env, res, l)
                                                      (_) -> let (storeP, envP, resP) = evalExp store env exp in
                                                             case resP of (Error x) -> (storeP, envP, resP, l)
                                                                          (_) -> (storeP, envP, resP, (resP:l))     


evalExpList :: Store -> Env -> [Exp] -> (Store,Env,Result,[Result])
evalExpList store env exps = let (storeP, envP, res, l) = foldl evalExpListAux (store,env,No,[]) exps in
                             case res of (Error x) ->  (storeP, envP, res, [])
                                         (_) -> (storeP, envP, res, (reverse l) )    

chackArg :: Store -> Env -> Arg -> Result -> Bool
chackArg store env (ArgType t  ident) res = case ( t, res ) of
                                                  (IntType, ResInt x) -> True
                                                  (StrType, ResStr x) -> True
                                                  (BoolType, ResBool x) -> True
                                                  (_) -> False

chackArg store env (ArgRef ref ident) res = case ( ref, res ) of
                                                  (IntRef, ResRefInt l) -> True
                                                  (StrRef, ResRefStr l) -> True
                                                  (BoolRef, ResRefBool l) -> True
                                                  (_) -> False 
convertResToPasArg :: Result -> PasArg
convertResToPasArg (ResInt x) =  Pat IntType
convertResToPasArg (ResStr x) =  Pat StrType
convertResToPasArg (ResBool x) = Pat BoolType
convertResToPasArg (ResRefStr loc) = Par StrRef
convertResToPasArg (ResRefInt loc) = Par IntRef
convertResToPasArg (ResRefBool loc) = Par BoolRef

convertArgToPasArg ::  Arg -> PasArg
convertArgToPasArg (ArgRef ref ident) = Par ref
convertArgToPasArg (ArgType t  ident) = Pat t

removeASpace:: String -> String
removeASpace [] = ""
removeASpace (',':xs) = xs    
removeASpace xs = xs

evalStmPrintAux :: (Store,Env,Result) -> String -> [Exp] -> (Store,Env,Result)
evalStmPrintAux (store,env,res) acc [] = ((printAdd store (removeASpace acc)),env,res)
evalStmPrintAux (store,env,(Error x)) acc l = (store,env,(Error x))  
evalStmPrintAux (store,env,No) acc (h:t) = let (storeP,envP,resP) = evalExp  store env h in 
                                       case resP of  (Error x) -> (storeP,env,resP)
                                                     (ResInt x) -> evalStmPrintAux (storeP,env,No) (acc ++ "," ++ (show x))  t
                                                     (ResStr x) -> evalStmPrintAux (storeP,env,No) (acc ++ "," ++ x)  t
                                                     (ResBool x) -> evalStmPrintAux (storeP,env,No)(acc ++ "," ++ (show x))  t
                                                     (_) -> (storeP,env,(Error "cant print this"))

printAdd :: Store->String ->Store
printAdd store s = let (Just (DList list)) = Map.lookup 0 store in Map.insert 0 (DList (s:list))  store

getPrint :: Store -> Data
getPrint store = let (Just list) = Map.lookup 0 store in list

getPrintList :: Store -> [String]
getPrintList store = let (DList l) = getPrint store in reverse(l)

putPrint :: Store -> Data -> Store
putPrint store (DList l) = Map.insert 0 (DList l) store

evalStmPack :: (Store,Env,Result) -> Stm -> (Store, Env,Result)
evalStmPack (store,env,res) stm = let (storeP, envP, resP) = evalStm store env stm in 
                                  case (res, resP) of ((Error x), _) -> (store,env,res)
                                                      (_, (Error x)) -> (store,env,resP)
                                                      (_, _) -> (storeP, envP, resP)
evalStmList :: [Stm] -> (Store, Env,Result)
evalStmList stms = foldl evalStmPack ( Map.fromList [(0,DList[] )], Map.fromList [(IdPrint, 0)],No) stms 

diffList :: [Loc] -> [Loc] -> [Loc]
diffList old new = go old new where
                   go o [] = []  
                   go [] (nh:nt) = nh:(go [] nt)
                   go (oh:ot) (nh:nt) = if oh == nh then 
                                                    go ot nt
                                                  else
                                                    if oh < nh then
                                                                  go ot (nh:nt)
                                                                else
                                                                  nh:(go (oh:ot) nt)  
cleanUpStore:: Store -> Env -> Env -> Store
cleanUpStore store oldEnv newEnv = let old = sort ( Map.elems oldEnv ) in
                                    let new = sort ( Map.elems newEnv ) in
                                      foldl (\store x-> Map.delete x store ) store (diffList old new)


evalBlkAux :: (Store, Env, Result) -> [Stm]  -> (Store, Env, Result)
evalBlkAux (store,env,x) ((Ret):t)   =  (store,env,No) 

evalBlkAux (store,env,x) ((RetVal exp):t)  =   evalStm store env (RetVal exp) 

evalBlkAux (store,env,No) (h:t) =  let (storeP,envP,ret) =  (evalStm store env h) in                          
                                   case ret of (Error x) -> (storeP,envP,ret)
                                               (ReturnBool x) -> (storeP,envP,ret) 
                                               (ReturnStr x) -> (storeP,envP,ret) 
                                               (ReturnInt x) -> (storeP,envP,ret) 
                                               (ReturnNono) -> (storeP,envP,ret) 
                                               (_)       ->  (evalBlkAux (storeP,envP,No)  t) 

evalBlkAux (store,env,No) [] = (store,env, No) 
cleanStore:: Store->Store->Store
cleanStore storeOld storeNew = let old =  Map.keys  storeOld in
                                let new =  Map.keys  storeNew in 
                                  foldl (\store x-> Map.delete x store ) storeNew (diffList old new)

evalBlk :: Store -> Env -> Block -> (Store, Env, Result)
evalBlk store env (Blk stms) = let (storeP, envP,ret) =  evalBlkAux (store, env, No) stms   in
                          ((cleanStore store storeP ),env,ret)

topStmToStm :: TopStm -> Stm
topStmToStm topstm = case topstm of 
                      DeclTop t items -> Decl t items
                      FunDecTop f -> FunDec f 
                      FunDefTop f block -> FunDef f block


loade :: Program -> (Store,Env,Result)
loade (Prog topstms) = let initStore = ( Map.fromList [(0,DList[] )]) in  
                        let initEnv = (Map.fromList [(IdPrint, 0)]) in
                          let stmList = map topStmToStm topstms in
                            evalBlkAux (initStore, initEnv, No) stmList

test :: [Stm] -> [String]
test stms = let initStore = ( Map.fromList [(0,DList[] )]) in  
                        let initEnv = (Map.fromList [(IdPrint, 0)]) in
                          let  (s, e, r )  = evalBlkAux (initStore, initEnv, No) stms in
                             ("RESULT PROGRAM = " ++ (show r ) ) :(programRaport s e)
printType:: Type-> String
printType IntType = "int"
printType StrType = "string"
printType BoolType = "bool"
printType VoidType = "void"

printRef:: Ref-> String
printRef IntRef = "int&"
printRef StrRef = "string&"
printRef BoolRef = "bool&"

printArg :: Arg -> String
printArg (ArgType t (Ident x)) =  printType t ++ " " ++ x 
printArg (ArgRef r (Ident x)) = printRef r ++ " " ++ x

printId :: Id -> String
printId (IdVar x) = "VAR: " ++ x  ++ " --- "
printId (IdFun x args) = "FUN: " ++ x ++ " --- "

printData :: Data -> String
printData (DInt x) = (show x) 
printData (DStr x) = x 
printData (DBool x) = (show x) 
printData (DFun t args e b) = (printType t) ++ " " ++ " ( " ++ (foldl (\s a -> s ++printArg a ++ ", " ) "" args)  ++ " ) "  

vv :: Store ->Env -> [String]
vv store env = let s = Map.delete 0 store in
                  let e = Map.delete IdPrint env in
                    map ( \id -> let (Just loc, Just d) = find_loc_data s e id in  
                          ( printId id) ++ (show loc) ++ " --> " ++ (printData d )  ) 
                   (Map.keys e)



programRaport :: Store->Env -> [String]
programRaport store env  = (vv store env)  ++  getPrintList (store)

evalProgram :: Program -> (String,[String])
evalProgram (Prog topstms) = let (store, env, res ) = loade (Prog topstms) in
                    let mainId = IdFun "main" [] in 
                      let (loc, main) = find_loc_data store env mainId in 
                        case (res,main) of
                          (Error x, _) -> ( "ERROR: " ++ x ,getPrintList (store))
                          (_, Nothing) -> ( "ERROR: can't find main function" ,getPrintList (store))
                          (_, Just fun) -> let (s,e,r) = (callFunctionMain store env [] fun) in 
                                          case r of ( Error x) ->  ( "ERROR: " ++ x ,(programRaport s e)++getPrintList (store))    
                                                    (ResInt x) -> ( "",(show x):getPrintList (s))
                                                    (ResStr x) -> ( "",(show x):getPrintList (s))
                                                    (ResBool x) -> ( "",(show x):getPrintList (s))
                                                    (_) -> ( "", getPrintList (s)) 

evalProgram (ProExp exp) = let initStore = ( Map.fromList [(0,DList[] )]) in  
                              let initEnv = (Map.fromList [(IdPrint, 0)]) in
                                let (s,e,r) = evalExp initStore initEnv exp in
                                  case r of (Error x) -> ( "ERROR: " ++ x ,getPrintList (s))
                                            (ResStr x) -> ( "",x:getPrintList (s))
                                            (ResBool x) -> ( "",(show x):getPrintList (s))
                                            (ResInt x) -> ( "",(show x):getPrintList (s))
                                            (ResRefStr loc) -> ( "", ("adres: " ++ (show loc)):getPrintList (s))
                                            (ResRefInt loc) -> ( "", ("adres: " ++ (show loc)):getPrintList (s))
                                            (ResRefBool loc) -> ( "", ("adres: " ++ (show loc)):getPrintList (s)) 
                                            (_) -> ( "", getPrintList (s))

printRes :: Result -> String
printRes (ResInt x) = "int"
printRes (ResStr x) = "string"
printRes (ResBool x) = "bool"

printRes (ResRefBool x) = "&bool"
printRes (ResRefInt x) = "&int"
printRes (ResRefStr x) = "&string"

printRes (No) = "void"
printRes (ReturnInt x) = "int"
printRes (ReturnStr x) = "str"
printRes (ReturnBool x) = "bool"
printRes (ReturnNono) = "void"
printRes (Error x) = "error"

printMulop :: MulOp ->String
printMulop Times = "*" 
printMulop Div  = "\\" 
printMulop Mod = "%"

printAddop :: AddOp ->String
printAddop Plus = "+" 
printAddop Minus  = "-" 

callFunctionMain :: Store -> Env ->  [Result] -> Data  -> (Store, Env, Result)
callFunctionMain store env args (DFun returnType argsTyps envF block) =  let (storeP, envP, res) = loadArguments (store, envF, No) args argsTyps in  
                                                                     case res of (Error x) -> (storeP, envP, res) 
                                                                                 (_) -> (let (s,e,r) =  (evalBlk storeP envP block) in
                                                                                          case  (returnType, r) of
                                                                                          (_, Error x) -> (s,e,Error x)
                                                                                          (IntType, ReturnInt x ) -> (s,e, (ResInt x)) 
                                                                                          (IntType, ReturnNono) -> (s,e,No)
                                                                                          (IntType, No) -> (s,e,No) 
                                                                                          (x,y) ->  (s,e,Error ("Wrong return type: expected:" ++ (printType x) ++ " get: " ++ printRes y)))  
