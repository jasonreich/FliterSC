> {-# LANGUAGE ParallelListComp, FlexibleInstances #-}
> module Fliter.Pretty where
> 
> import Control.Arrow (first)
> import Text.PrettyPrint.Leijen
> 
> import Fliter.Syntax
> 
> braceSemiFront = align . encloseSep (lbrace <> space) (space <> rbrace) (semi <> space)
> intermap f [] = []
> intermap f [x] = [x]
> intermap f (x:xs) = f x : intermap f xs
> braceSemiEnd xs = lbrace <$> (vsep . intermap (<> text ";" <> line)) xs <$> rbrace
>
> varSupply = [ c : i | i <- "" : map show [0..], c <- "xyzpqrijkmn"]
> 
> prettyOp Pl = text "+"
> prettyOp Mi = text "-"
> prettyOp Eq = text "=="
> prettyOp Ne = text "/="
> prettyOp Le = text "<="
> prettyOp Seq = text "`seq`"
> 
> zipDrop :: [a] -> [b] -> ([(a, b)], [a])
> zipDrop xs [] = ([], xs)
> zipDrop (x:xs) (y:ys) = first ((x, y):) $ zipDrop xs ys
> 
> prettyVar (Fre v) = text v
> prettyVar (Bnd i) = text $ '#' : show i
> 
> prettyExpr :: [String] -> Expr' t String -> Doc
> prettyExpr fresh (Var v)     = prettyVar v
> prettyExpr fresh (Fun f [])  = text f
> prettyExpr fresh (Fun f vs)  = prettyExpr fresh $ (undefined :> Fun f []) :@ map (Fre . ('@':)) vs
> prettyExpr fresh (Con c [])  = text $ c
> prettyExpr fresh (Con c vs)  = prettyExpr fresh $ (undefined :> Con c []) :@ map (Fre . ('@':)) vs
> prettyExpr fresh (PVa n)     = text $ show n
> prettyExpr fresh (POp o v w) = hsep [prettyVar v, prettyOp o, prettyVar w]
> prettyExpr fresh (x :@ vs)   = hsep ((prettyExpr fresh . getRhs) x : map prettyVar vs)
> prettyExpr fresh (Let xs y)  = align $ text "let" <+> braceSemiFront bindings <$> 
>                                        text "in" <+> align ((prettyExpr fresh' . getRhs) $ close vs y)
>   where bindings = [ text v <+> text "=" <+> align (prettyExpr fresh . getRhs $ x)
>                    | (v, x) <- bs ]
>         (bs, fresh') = zipDrop fresh xs
>         vs = map fst bs
> prettyExpr fresh (Case x as)   = nest 2 $ text "case" <+> align ((prettyExpr fresh . getRhs) x) <+> text "of" <$>
>                                           (braceSemiFront . map (prettyAlte fresh) $ as)
>                                
> prettyAlte :: [String] -> Alte t String -> Doc
> prettyAlte fresh ((c, novs) :-> y)
>   = text c <+> text (unwords vs) <+> text "->" <+>
>     (prettyExpr fresh' . getRhs $ close vs y)
>   where (vs, fresh') = splitAt novs fresh
>                                
> prettyFunc :: Func t String -> Doc
> prettyFunc (Lam novs x) = text "\\" <+> text (unwords vs) <+> text "->" <+>
>                           (prettyExpr fresh . getRhs) (close vs x)
>   where (vs, fresh) = splitAt novs varSupply
>         
> prettyProg :: Prog t String -> Doc
> prettyProg (Prog p) = braceSemiEnd $
>                       [ text f <+> text (unwords vs) <+> text "=" <+>
>                              (prettyExpr fresh . getRhs) (close vs x)
>                            | (f, Lam novs x) <- p
>                            , let (vs, fresh) = splitAt novs varSupply ]
> 
> wrap x = "[" ++ show x ++ "]"
> 
> instance Show a => Show (Prog t a) where
>   showsPrec _ = displayS . renderPretty 0.4 60 . prettyProg . fmap wrap
>   
> instance Show a => Show (Func t a) where
>   showsPrec _ = displayS . renderPretty 0.4 60 . prettyFunc . fmap wrap
>   
> instance Show a => Show (Expr' t a) where
>   showsPrec _ = displayS . renderCompact . prettyExpr varSupply . fmap wrap
>   
> instance Show a => Show (Alte t a) where
>   showsPrec _ = displayS . renderCompact . prettyAlte varSupply . fmap wrap
