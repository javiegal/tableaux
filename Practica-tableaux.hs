-- Javier Gallego Gutiérrez
-- Práctica tableaux

data FProp = Cierto | Falso | P String | No FProp | Y FProp FProp | O FProp FProp deriving (Show, Read)

-- FProp como instancia de Eq siendo la igualdad entre fórmulas la igualdad estructural sin atender al orden
instance Eq FProp where
 x == y = x `igualdadEstruct` y
 
-- FProp como instancia de la clase Ord. phi <= phi' si phi implica phi'
instance Ord FProp where
 x <= y = consecuencia y [x]

-- función igualdad estructural
igualdadEstruct:: FProp -> FProp -> Bool
igualdadEstruct Cierto Cierto = True
igualdadEstruct Falso Falso = True
igualdadEstruct (P x) (P y) = x == y
igualdadEstruct (No x) (No y) = igualdadEstruct x y
igualdadEstruct (Y x y) (Y z t) = (igualdadEstruct x z && igualdadEstruct y t) || (igualdadEstruct x t && igualdadEstruct y z)
igualdadEstruct (O x y) (O z t) = (igualdadEstruct x z && igualdadEstruct y t) || (igualdadEstruct x t && igualdadEstruct y z)
igualdadEstruct x y = False

-- función sigma
-- Reduce la fórmula si es simplificable
sigma:: FProp -> FProp
sigma (No Cierto) = Falso
sigma (No Falso) = Cierto
sigma (No (No a)) = a
sigma a = a

-- función sigmareglas
-- Devuelve la lista formada por la aplicación de sigma a cada uno de los elementos de otra lista
sigmareglas:: [FProp] -> [FProp]
sigmareglas [] = []
sigmareglas (x:xs) = [sigma x] ++ sigmareglas xs

-- función alpha
-- Reduce la fórmula si es conjuntiva devolviendo las fórmulas resultantes en una lista
alpha:: FProp -> [FProp]
alpha (Y a b) = [a,b]
alpha (No (O a b)) = [(No a), (No b)]
alpha a = [a]

-- función alphareglas
-- Devuelve la lista formada por la aplicación de alpha a cada uno de los elementos de otra lista
alphareglas:: [FProp] -> [FProp]
alphareglas [] = []
alphareglas (x:xs) = alpha x ++ alphareglas xs

-- función beta
-- Reduce la fórmula si es disyuntiva devolviendo las fórmulas resultantes en una lista
beta:: FProp -> [FProp]
beta (O a b) = [a,b]
beta (No (Y a b)) = [(No a),(No b)]
beta a = []

-- función betareglas
-- Devuelve la lista formada por las dos listas que se obtienen al aplicar beta al primer elemento que abre dos ramas distintas.
-- Si no existe tal elemento, se devuelve una lista que contiene a la lista inicial
betareglas:: [FProp] -> [[FProp]]
betareglas [] = []
betareglas (x:xs)
 | a == [] = map ([x] ++) (betareglas xs)
 | otherwise = [[a !! 0] ++ xs, [last a] ++ xs]
 where a = beta x

-- función contradicción: True si en el conjunto de fórmulas encontramos dos que sean A y ¬A, False en caso contrario
contradiccion:: [FProp] -> Bool
contradiccion [] = False
contradiccion (Cierto:xs) = elem Falso xs || contradiccion xs
contradiccion (Falso:xs) = elem Cierto xs || contradiccion xs
contradiccion (x:xs) = elem (No x) xs || contradiccion xs


-- función tableau_cerrado
-- Comprueba si hay dos fórmulas contradictorias (A y ¬A) o alguna es la fórmula Falso. En caso afirmativo, devuelve True (se ha cerrado el tableau).
-- Si no, calcula el tableau_cerrado de la lista tras aplicarle las sigmareglas (siempre que las sigmareglas modifiquen el conjunto de fórmulas).
-- Si las sigmareglas no modifican la lista, se hace los mismo para las alphareglas.
-- En caso de que las alphareglas tampoco modifiquen la lista, pasamos a las betareglas.
-- Si las betareglas no modifican la lista, se devuelve False porque la rama se ha terminado.
-- Si las betareglas modifican la lista, se devuelve la AND lógica de los resultados de aplicar tableau_cerrado a las distintas ramas abiertas.
tableau_cerrado:: [FProp] -> Bool
tableau_cerrado xs =
 if contradiccion xs || elem Falso xs == True then True else
 if xs /= a then tableau_cerrado a else
 if xs /= b then tableau_cerrado b else
 if length c > 1 then and (map tableau_cerrado c) else False
 where {a = sigmareglas xs ; b = alphareglas xs ; c = betareglas xs}


-- función tautología
-- Comprueba si la negación de la fórmula tiene un tableau cerrado.
tautologia:: FProp -> Bool
tautologia a = tableau_cerrado [(No a)]

-- función consecuencia
-- Comprueba que el conjunto de fórmulas b unión {¬a} tiene un tableau cerrado.
consecuencia:: FProp -> [FProp] -> Bool
consecuencia a b = tableau_cerrado (b++[(No a)])

-- función equivalentes
-- Comprueba si (¬a or b)^(¬b or a) es una tautología
equivalentes:: FProp -> FProp -> Bool
equivalentes a b = tautologia (Y (O (No a) b) (O (No b) a))

-- fórmulas
f1 = O (Y (P "p") (No (P "q"))) (No (P "p"))
f2 = O (No Falso) (Y (P "p") (No (O (P "q") (No (P "q")))))
f3 = Y (Y Cierto (P "q")) (O (No (P "q")) (P "r"))
f4 = O (No(P "r")) (O (No(P "p")) (No (P "q")))
f5 = No (Y (O (Cierto) (P "p")) (O (P "q") Falso))

-- Menú
-- Pide las fórmulas y da tres opciones posibles para trabajar con ellas
menu:: IO ()
menu = do
 putStrLn "Introduce las fórmulas (una por línea y XXX para acabar):"
 formulas <- obtenerLista
 let lista_formulas = map read formulas::[FProp]
 putStrLn "0 - Comprobar cuáles son tautologías." 
 putStrLn "1 - Comprobar si la primera es consecuencia del resto."
 putStrLn "2 - Comprobar si la primera y la segunda fórmula son equivalentes."
 c <- getChar
 case c of
  '0' -> print (map tautologia lista_formulas)
  '1' -> print (consecuencia (head lista_formulas) (tail lista_formulas))
  '2' -> print (equivalentes (lista_formulas !! 0) (lista_formulas !! 1))
 
-- función obtenerLista 
-- Permite obtener una lista de String a partir de la entrada de varios String línea a línea terminando con "XXX"
obtenerLista:: IO [String]
obtenerLista = do
 formula <- getLine
 if formula == "XXX" then return [] else obtenerLista >>= \x -> return (formula:x)