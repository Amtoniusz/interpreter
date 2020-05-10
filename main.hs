module Main where
 
import Data.Map (Map)
import qualified Data.Map as Map 
import LexGramatyka
import ParGramatyka
import AbsGramatyka
import Interpreter
import Debug.Trace
import ErrM
debug = flip trace



-- Map.fromList [(0,DList[] )]
-- Map.fromList [(IdPrint, 0)]
boolToString :: Bool -> String
boolToString True = "TRUE"
boolToString False = "FALSE"
testExp :: Exp -> Result -> String
testExp exp res = case (eval exp) of
        Error s -> "ERROR " ++ s
        e ->  boolToString   ( e == res )

tesStmList :: [Stm] -> Result ->String
tesStmList stms res  = case (evalStmList stms) of
        (_,_,(Error s)) -> "ERROR " ++ s
        (_,_,e) ->  boolToString   ( e == res )
evalBlkTest:: Block -> (Store,Env,Result)        
evalBlkTest = evalBlk (Map.fromList [(0,DList[] )]) (Map.fromList [(IdPrint, 0)])

getValueInt :: Store -> Env -> String -> Integer
getValueInt store env s = let  (loc,d) = find_loc_data store env (IdVar s) in case d of
                                                                                (Just (DInt x)) -> x
                                                                                _ -> (-12)

checkSizes :: Store -> Env -> Integer -> Bool
checkSizes store env size = let storeSize = toInteger $ Map.size store in
                            let envSize = toInteger $ Map.size env in storeSize == size && envSize == size
main :: IO ()
main = do   
    putStrLn (testExp (EAdd (EInt 1) Plus (EInt 4)) (ResInt 5))
    putStrLn (testExp (EAdd (EInt 1) Plus (EMul (EInt 4) Div (EInt 2))) (ResInt 3))
    putStrLn (testExp (ERel (EAdd (EInt 1) Plus (EMul (EInt 4) Div (EInt 2))) EQU (EInt 3)) (ResBool True ))
    let x = (EOr (ERel (EAdd (EInt 1) Plus (EMul (EInt 4) Div (EInt 2))) LE (EInt 3)) EFalse) in
        let y = (ResBool True) in 
            putStrLn (testExp x y)        
    let x = [Decl IntType [Init (Ident "a") (EInt 1)],StmExp (EAdd (EIdent (Ident "a")) Plus (EInt 10))]in
        let y = (ResInt 11) in 
            putStrLn (tesStmList x y) 
    let x = [Decl IntType [Init (Ident "b") (EInt 0)],Decl IntType [Init (Ident "a") (EInt 10)],While (ERel (EIdent (Ident "a")) GTH (EInt 0)) (Blk [Ass (Ident "b") (EAdd (EIdent (Ident "b")) Plus (EInt 2)),Ass (Ident "a") (EAdd (EIdent (Ident "a")) Minus (EInt 1))])] in 
            let (store,env,res) = evalStmList x in  do
                putStrLn (show (checkSizes store env 3));
                putStrLn (show (res == No));
                putStrLn ( show ( (getValueInt store env "a")  == 0) );            
                putStrLn ( show ( (getValueInt store env "b")  == 20) );   
    let x = [Decl IntType [Init (Ident "b") (EInt 0)],Decl IntType [Init (Ident "a") (EInt 10)],While (ERel (EIdent (Ident "a")) GTH (EInt 0)) (Blk [Decl IntType [Init (Ident "c") (EInt 12)],Ass (Ident "b") (EAdd (EIdent (Ident "b")) Plus (EInt 2)),Ass (Ident "a") (EAdd (EIdent (Ident "a")) Minus (EInt 1))])] in 
            let (store,env,res) = evalStmList x in  do
                putStrLn (show (checkSizes store env 3));
                putStrLn (show (res == No));
                putStrLn ( show ( (getValueInt store env "a")  == 0) );            
                putStrLn ( show ( (getValueInt store env "b")  == 20) );
    let x = [Decl IntType [Init (Ident "b") (EInt 0)],Decl IntType [Init (Ident "a") (EInt 10)],While (ERel (EIdent (Ident "a")) GTH (EInt 0)) (Blk [Decl IntType [Init (Ident "c") (EInt 1)],Ass (Ident "b") (EAdd (EIdent (Ident "b")) Plus (EIdent (Ident "c"))),Ass (Ident "a") (EAdd (EIdent (Ident "a")) Minus (EInt 1))])]in 
            let (store,env,res) = evalStmList x in  do
                putStrLn (show (checkSizes store env 3));
                putStrLn (show (res == No));
                putStrLn ( show ( (getValueInt store env "a")  == 0) );            
                putStrLn ( show ( (getValueInt store env "b")  == 10) );
    let x = ([FunDef (FunPref IntType (Ident "foo") [ArgType IntType (Ident "a")]) (Blk [RetVal (EAdd (EIdent (Ident "a")) Plus (EInt 1))]),Decl IntType [Init (Ident "x") (EInt 1)],Decl IntType [Init (Ident "y") (EFun (Ident "foo") [EIdent (Ident "x")])]]) in 
            mapM_ print (test x)            