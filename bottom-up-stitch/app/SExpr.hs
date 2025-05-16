module SExpr where

data SExpr = SExpr String [SExpr] deriving (Show, Eq)
data ParseError = Expected String deriving (Show, Eq)

lexSExpr:: [String] -> String -> [String]
lexSExpr buf [] = map reverse $ filter (/= "") (reverse buf)
lexSExpr buf (x:xs) = case x of
    '(' -> lexSExpr ("":"(":buf) xs
    ')' -> lexSExpr ("":")":buf) xs
    ' ' -> lexSExpr ("":buf) xs
    _   -> lexSExpr ((x:head buf):tail buf) xs

parseLexed:: [String] -> Either ParseError (SExpr, [String])
parseLexed ("(":sym:xs) = do
    (e, xs') <- parseSeveral xs
    case xs' of
        (")":xs'') -> Right (SExpr sym e, xs'')
        _ -> Left (Expected ")")
parseLexed (sym:xs) = Right (SExpr sym [], xs)
parseLexed _ = Left (Expected "something")

parseSeveral:: [String] -> Either ParseError ([SExpr], [String])
parseSeveral (")":xs) = Right ([], ")":xs)
parseSeveral xs = do
    (e, xs') <- parseLexed xs
    (es, xs'') <- parseSeveral xs'
    return (e:es, xs'')

parse':: String -> Either ParseError SExpr
parse' x = fmap fst . parseLexed $ lexSExpr [] x

parse :: String -> SExpr
parse x = case parse' x of
    Left err -> error (show err)
    Right e  -> e

render:: SExpr -> String
render (SExpr sym []) = sym
render (SExpr sym children) = "(" ++ sym ++ " " ++ unwords (map render children) ++ ")"