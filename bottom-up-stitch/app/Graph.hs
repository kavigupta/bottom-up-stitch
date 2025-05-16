module Graph where

import Data.Map.Strict (Map, empty, insert, toList, insertWith)

import SExpr

data Graph = Graph { symbolArityOf:: Map Int (String, Int),
    childrenOf:: Map Int [Int],
    newId:: Int} deriving (Show, Eq)

emptyGraph:: Graph
emptyGraph = Graph {
    symbolArityOf = empty,
    childrenOf = empty,
    newId = 0
}

addSExpr:: SExpr -> Graph -> (Int, Graph)
addSExpr (SExpr sym children) g = 
    let
        (idents, g'') = addSExprs children g'
        (ident, g') = addSymbol sym idents g
    in
        (ident, g'')

addSExprs:: [SExpr] -> Graph -> ([Int], Graph)
addSExprs s0 g0 = 
    foldr (\s (ids, g) -> let (ident, g') = addSExpr s g in (ident:ids, g')) ([], g0) s0

addSymbol:: String -> [Int] -> Graph -> (Int, Graph)
addSymbol sym childrenIds (Graph symArity children nId) =
    let
        symArity' = insert nId (sym, (length childrenIds)) symArity
        children' = insert nId childrenIds children
        nId' = nId + 1
    in
        (nId, Graph symArity' children' nId')

type SymbolArityToLocations = [((String, Int), [Int])]

computeSymbolArityToLocation:: Graph -> SymbolArityToLocations
computeSymbolArityToLocation (Graph symArity _ nId) = result
    where
    backMap:: Map (String, Int) [Int]
    backMap = foldr (\(id, (sym, arity)) m -> insertWith (++) (sym, arity) [id] m) empty (toList symArity)
    result = toList backMap