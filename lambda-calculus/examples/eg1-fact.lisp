(-- f (\ D x (* D x x)))
(-- hundred ($ D f 10))

(decl mul (\ D a (\ D b (* S a b))))
(-- TODO: automatically call `lift` if possible)
(decl test ($ D ($ D mul (lift 3)) (lift 4))) 


(decl pow (\ D rec (\ D n (\ D x (if D (== D n 0) 1 (* D x ($ D ($ D rec (- D n 1)) x)))))))
(decl snd (\ D n (\ D x x)))

(decl cube ($ D ($ D pow ($ D pow snd)) 3))
(decl testCube ($ D cube 5))

(decl powS (\ D rec (\ D n (\ D x (if D (== D n 0) (lift 1) (* S x ($ D ($ D rec (- D n 1)) x)))))))
(decl sndS (\ D n (\ D m (lift 40))))

(decl cubeS ($ D ($ D powS ($ D powS sndS)) 3))
(decl testCubeS (\ S y ($ D cubeS y)))
