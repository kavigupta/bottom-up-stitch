module Bus where

import Data.Map.Strict ((!), toList)
import Data.List (sort)

import SExpr
import Graph


data Match = Match { 
    treeOf::SExpr,
    utilityOf::Int,
    locationsOf::[Int],
    iterationAddedOf::Int} deriving (Show, Eq)

initialMatch:: [Int] -> Match
initialMatch locations = Match {
    treeOf = SExpr "?" [],
    utilityOf = 0,
    locationsOf = locations,
    iterationAddedOf = -1
}

updateMatches:: Graph -> SymbolArityToLocations -> Int -> [Match] -> [Match]
updateMatches graph satl iter matches = paretoOptimize $ matches ++ do
    ((symbol, arity), locations) <- satl
    matchesEach graph iter matches symbol arity locations

(+>=):: Match -> Match -> Bool
(+>=) m1 m2 = (utilityOf m1 >= utilityOf m2) && superSet (locationsOf m1) (locationsOf m2)

superSet:: [Int] -> [Int] -> Bool
superSet xs ys = all (`elem` xs) ys


paretoOptimize:: [Match] -> [Match]
paretoOptimize [] = []
paretoOptimize (x:xs)
    | isDominated = paretoOptimize xs
    | otherwise = x : paretoOptimize (filter (\m -> not (x +>= m)) xs)
    where
        isDominated = any (x +>=) xs

cartProduct:: [a] -> Int -> [[a]]
cartProduct _ 0 = [[]]
cartProduct xs n = do
    x <- xs
    xs' <- cartProduct xs (n - 1)
    return (x:xs')

-- | Given a graph, a list of matches, a set of locations, and a child index, returns a list of matches, along with the locations of the children of the match at the given index.
childMatches:: Graph -> [Match] -> [Int] -> Int -> [(Match, [Int])]
childMatches graph matches locations childIndex = undefined
    where



matchesEach:: Graph -> Int -> [Match] -> String -> Int -> [Int] -> [Match]
matchesEach graph iter matches symbol arity locations = do
        submatches <- allSubmatches
        let consistentLoc loc = let children = childrenOf graph ! loc in all (\(m, i) -> (children !! i `elem` locationsOf m)) (zip submatches [0..])
        let filteredLocs = filter (consistentLoc) locations
        if (length filteredLocs < 2) then []
        else
            return $ Match {
                treeOf = SExpr symbol (map treeOf submatches),
                utilityOf = 1 + sum (map utilityOf submatches),
                locationsOf = filteredLocs,
                iterationAddedOf = iter
            }
    where
    allSubmatches = cartProduct matches arity

bus' :: Graph -> SymbolArityToLocations -> Int -> [Match] -> [[Match]]
bus' graph satl iter matches
    | same = [matches]
    | otherwise = matches: bus' graph satl (iter + 1) updated
    where
        updated:: [Match]
        updated = updateMatches graph satl iter matches
        same = sort (map (show .treeOf) matches) == sort (map (show .treeOf) updated)

bus :: Graph -> [[Match]]
bus graph = bus' graph (computeSymbolArityToLocation graph) 0 [initialMatch (map fst (toList (childrenOf graph)))]