(decl powS (\ D rec (\ D n (\ D x (if D (== D n 0) (comptime 1) (* S x ($ D ($ D rec (- D n 1)) x)))))))
(decl powFix (fix D powS))
(decl testPow3Fix (\ S y ($ D ($ D powFix y) 3)))

