  (decl power 
    ($ D ($ D (fix S 
          (\ S p (\ S n (\ S x
                (if D 
                  (== D n 0)
                  (lift 1)
                  (* D n ($ D p (- D n 1))))))))
                  2) 10))
