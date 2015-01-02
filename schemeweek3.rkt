(require racket/vector)

(define MAX_NUMBER 100)
;-----------------------------------------------------------------------------
;Backtracking
;-----------------------------------------------------------------------------

;Counter for the number of queen shifts required for a backracking method on a given board
(define counter 0)

(define (backtracking n)
  (let ((v (make-vector n -1)))
    (begin (inbacktracking2 v -1)
           (newline)
           (display counter)
           (set! counter 0)))) ;resetting the counter to 0

(define v1 #(0 2 4 1 3))

(define (inbacktracking2 state currcol)
  (if (eq? (vector-ref state (- (vector-length state) 1)) -1) ;if the value in the last column is '-1' then we have not yet reached a solution
      (let ((col (+ 1 currcol)))
        (do ((row 0 (+ row 1))) ;for every row
          ((eq? row (vector-length state)) #f)  ;if this is true then we have nowhere to put a queen in that row
          (if (and (not (vector-member row state)) ;if the potential row is not already taken by another queen
                   (let loop ((j 0)) ;transversing through the columns to check for no diagonal attack
                     (if (or (eq? (+ (vector-ref state j) (- col j)) row) ;if there is a down-right collison or
                             (eq? (- (vector-ref state j) (- col j)) row)) ;an up-rght collision
                         #f
                         (if (eq? col j) ;if we have traversed through each existing queen and found no collisions then return true
                             #t
                             (loop (+ 1 j)))))) ;endand 
              (begin (vector-set! state col row)
                     (set! counter(+ counter 1))
                     ;(display state)
                     (if (not (eq? (inbacktracking2 state col) #f)) 
                         state
                         (begin (vector-set! state col -1)
                                (set! counter(+ counter 1))))))))
      (begin (let loopy ((k 0)) ;removing the left-over part answers from the recursion and only displaying the final
               (if (eq? (- (vector-length state) 1) k)
                   (display state)
                   (if (not (eq? -1 (vector-ref state k)))
                      (loopy (+ 1 k))))))))   


;Alternative version
#|
this function is called by the user, uses num to create an empty vector,
calls the internal backtracking function,
prints out the resultant board
and displays the number of total queen movements
|#
(define nq-bt   
  (lambda (num)
    (let ((vec (make-vector num -1)))
      (back-internal vec 0)
      (print-vector vec)
      (printf "~a\n" counter)
      (set! counter 0))))
#|internal backtracking function that calls onto itself until the correct board is found|#
(define back-internal
  (lambda (vec col)
    (if (eq? #f (vector-member -1 vec)) ;return the board when there are no more empty columns
        vec
        (if (eq? col (vector-length vec)) ;if you reach the end of the board with empty columns, you're doign it wrong
            #f
            (if (eq? -1 (vector-ref vec col)) ;if current column is empty, start checking where a queen can be placed row by row
                (do ((row 0 (+ 1 row)))
                  ((or (not (eq? -1 (vector-ref vec col))) ;stop either when the column is not empty anymore or there are no more rows to check
                       (eq? row (vector-length vec)))
                   (if (not (eq? -1 (vector-ref vec col)))
                       #t
                       #f))
                  (if (eq? #f (vector-member row vec)) ;horizontal conflict check
                      (if (do ((counter-col 0 (+ 1 counter-col))) ;checks for the diagonal conflicts
                            ((or (eq? counter-col col)
                                 (eq? (abs (- col counter-col)) (abs (- row (vector-ref vec counter-col)))))
                             (if (eq? (abs (- col counter-col)) (abs (- row (vector-ref vec counter-col))))
                                 #f
                                 #t)))
                          (and (vector-set! vec col row) ;if there are no collisions registered at this row, place a queen there and traverse down to the next column
                               (set! counter (+ 1 counter))
                               #|(printf "placed a queen in col ~a row ~a vector ~a\n"
                                            col
                                            row
                                            vec)|#
                               (if (not (eq? #f (back-internal vec (+ 1 col)))) ;if this placement doesn't work with the succeeding columns, go back
                                   (back-internal vec (+ 1 col))
                                   (and (vector-set! vec col -1)
                                        (set! counter (+ 1 counter))
                                        #|(printf "took a queen out of column ~a ~a\n"
                                                     col
                                                     vec)|#)))))))))))


;-----------------------------------------------------------------------------
;Hill Climbing - Min Conflicts
;-----------------------------------------------------------------------------



;Initializing the column to minimize conflicts for odd numbered boards
(define (initialize n) ;n is the number of slots in a chess board
  (let ((m (floor (/ (- n 1) 2)))
        (v (make-vector n -1)))
    (begin (do ((i 0 (+ i 1)))
             ((= i (+ m 1))) ;when this is true - we have filled the vertex with the even placed queens
             (vector-set! v i (* i 2)))
           (do ((i 0 (+ i 1)))
             ((= (+ (+ m 1) i) n) v)
             (vector-set! v (+ (+ m 1) i) (+ (* i 2) 1))))))


;Counter for the number of steps it took to get an initialez board to a goal state
(define min_con_steps 0)

;Returns true if a given vertex contains no conflicting queens and false otherwise
(define (goal v) 
  (let loop ((i 0))
    (if (eq? i (- (vector-length v) 1))
        #t ;no conflict found
        (if (let loopy ((j (+ i 1))) 
              (if (eq? j (vector-length v))
                  #t ;if the checker is at the last column then all the checks on an attack on ith queen have been done, otherwise...
                  (if (conflict? i (vector-ref v i) j (vector-ref v j))
                  #f
                  (loopy (+ 1 j)))))
            (loop (+ 1 i)) ;if no conflict found for ith queen - keep checking
            #f)))) ;otherwise there is a conflict
            
;Finding a conflict between two queens based on a diagonal rule - mathematically checking if two points lie on a same diagonal line
(define (conflict? col1 row1 col2 row2)
  (if (or (eq? (+ row1 (- col2 col1)) row2)
          (eq? (- row1 (- col2 col1)) row2)
          (eq? row1 row2))
      #t
      #f))

;Making a vector equal to the size of the largest board that this program will be tested on
(define conflicting_colums (make-vector MAX_NUMBER 0))


;Updating a vector containing conflicflicting columns (1) and non-cloflicting columns (0)
(define (update_c_columns v)
  (begin (vector-fill! conflicting_colums 0) ;resetting the global variable to all 0s
         (let loop ((i 0))
           (if (not (eq? i (- (vector-length v) 1))) ;while we have not reached then end
               (begin (let loopy ((j (+ i 1))) 
                        (if (not (eq? j (vector-length v))) ;while we have not reached the last column 
                                   (begin (if (conflict? i (vector-ref v i) j (vector-ref v j)) ;if a conflict was found
                                              (begin (vector-set! conflicting_colums i 1)
                                                     (vector-set! conflicting_colums j 1))) ;we reset the value corresponding to a column with a found conflict from 0 to 1
                                       (loopy (+ 1 j))))) ;we don't need to keep checking when we find a conflict (0 and 1 system)
                      (loop (+ 1 i))))))) ;keep checking for conflicts until the if fails
    


;Choosing a random conflicting column from the updated conflicitng column vector (conflicting_colums)
(define (choose_col n)
  (let ((count_col 0) ;the number of conflicting colums
        (random_col 0)
        (m 0))
    (begin (do ((i 0 (+ i 1)))
             ((eq? i n)) ;stop when reach the end of vector
             (if (eq? 1 (vector-ref conflicting_colums i)) ;those columns where the value is 1 - there is a conflict
                 (set! count_col(+ count_col 1)))) ;we count them to later make a another vector containing those
           (let ((random_num (random count_col))
                 (result (make-vector count_col -1))) 
             (begin (let loop ((k 0))
                      (if (not (eq? k count_col)) ;while we have not reached the end of column to place conflicting columns 
                          (begin (if (eq? k 0)
                                     (set! m k)
                                     (set! m (- k 1)))
                                 (let loopy ((j (+ (vector-ref result m) 1))) ;we always start j one slot in front of the lastly added 1 to the list 
                                   (if (not (eq? j n)) ;while we have not reached the end of the conflicting columns
                                       (if (eq? 1 (vector-ref conflicting_colums j)) ;when we find a conflicting column in the vector list
                                           (begin (vector-set! result k j) ;we set i to the num of the col (j) from the main list
                                                  (loop (+ k 1)))
                                           (loopy (+ j 1)))))))) ;if we don't find 1 - we move forward
                    (set! random_col(vector-ref result random_num))))
           random_col))) ;finally returning a random column


;In case of infinite loops for boards of certain size (e.g. 6) a tie breaker was used. So there is a 1/10 chance that instead of a minimum row
;the program will choose ANY row 
(define tie_breaker_num 10)

;This function recieves the state that the board is at, its size, a random column and finds a row with the
;lowest conflict_count in the column. This is done by randomly choosing a column on the board and then using the first
;column with the lowest collisions encountered
(define (choose_row state n column)
  (let ((value_list (make-vector n -1))
        (conflict_count 0)
        (tie_breaker_random_num (random 11)))
    (if (eq? tie_breaker_random_num tie_breaker_num)
        (random n) ;there is a 1/10 chance that the column chosen will be random, and not the minimal one to break ties
        (begin (do ((row 0 (+ row 1))) ;filling up the value_list with the number of conflicts for each row 
                 ((eq? row n)) ;stop when reached the end
                 (begin (do ((col 0 (+ col 1)))
                          ((eq? col n)) ;stop when reached the end
                          (if (not (eq? col column)) ;skipping its own column 
                              (if (conflict? column row col (vector-ref state col)) ;if there is a conclict between two queens
                                  (begin (set! conflict_count (+ 1 conflict_count)) 
                                         (vector-set! value_list row conflict_count)))))
                        (set! conflict_count 0))) ;resetting the count to 0 after we are done with one row
               (choose_row2 value_list)))))
                 
            
;Look at a pseudocode for if unclear what this does
(define (nq-mc n) ;x for col
  (let ((col 0)
        (row 0))
    (let loop ((state (initialize n)))
      (if (goal state) ;if the current state equals its final state (no attacking queens) then we are done
          (begin (printf "steps: ~a \n" min_con_steps)
                 (print-vector state)
                 (set! min_con_steps 0)) ;resetting the counter) ;otherwise...
          (begin ;(print-vector state)
                 (set! min_con_steps (+ min_con_steps 1)) ;updating the number of steps it takes to rearrange this board
                 (update_c_columns state) ;updating the current conflicting columns in the state
                 (set! col (choose_col n))
                 (set! row (choose_row state n col))
                 ;(printf "chose col: ~a and row: ~a \n" col row)
                 (vector-set! state col row)
                 (loop state))))))

;Given a vector (column) it finds a random conflicting column
(define choose_row2
  (lambda (vec)
    (let ([holder (vector -1)] [min-num (apply min (vector->list vec))])
    (do ((pos-vec (vector) (vector-append pos-vec holder)))
      ((eq? #f (vector-member min-num vec))
        (vector-ref pos-vec (random (vector-length pos-vec))))
      (vector-set! holder 0 (vector-member min-num vec))
      (vector-set! vec (vector-member min-num vec) (vector-length vec))))))

(define print-vector
  (lambda (vec)
    (do ((row 0 (+ 1 row)))
      ((eq? row (vector-length vec)))
      (do ((col 0 (+ 1 col)))
        ((eq? col (vector-length vec))
         (display "\n"))
        (if (eq? row (vector-ref vec col))
            (display "1 ")
            (display "0 "))))))

     