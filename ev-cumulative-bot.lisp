;; #!/usr/local/bin/sbcl --script

(cl:let ((quicklisp-init (merge-pathnames "/home/michael/quicklisp/setup.lisp"
                                       (user-homedir-pathname))))
  (when (probe-file quicklisp-init)
    (load quicklisp-init)))

(ql:quickload '(:private :cl-ppcre) :silent t)

(in-package :>)
(syntax:use-syntax :clamp)
(shadow '(:split))

(use-package :cl-ppcre)


(= *random-state* (make-random-state t))

(defstruct (card (:conc-name nil) (:type list) (:constructor make-card (rank suit)))
  rank suit)

(defparameter ranks* '(a k q j 10 9 8 7 6 5 4 3 2)
  "A list of all of the ranks.")

(defparameter suits* '(c d h s)
  "A list of all of the suits.")

(mac hand-match (var hand &body clauses)
  "Does the hand satisify one of the hand patterns."
  (once-only (hand)
    `(iflet ,var
       ,@(mappendeach ((flush straight . ranks) body) (group clauses :by 2)
           `((hand-is ,hand ,flush ,straight ',ranks) ,body)))))

(def hand-is (hand flush straight ranks)
  "Test the hand depending on the other arguments. If FLUSH, test if
   the hand contains a flush. If STRAIGHT, test if the hand contains a
   straight. Test the rank counts matches RANKS. Return the score of
   the hand if the hand matches."
  (and (or (not flush) (flush hand))
       (or (not straight) (straight hand))
       (ranks-are hand ranks)))

(def convert (rank)
  "Converts a rank to a number."
  (case rank a 14 k 13 q 12 j 11 t rank))

(def rank< (x y)
  "Is the first rank less than the second?"
  (< (convert x) (convert y)))

(def rank> (x y)
  "Is the first rank greater than the second?"
  (> (convert x) (convert y)))

(def flush (hand)
  "Does this hand contain a flush?"
  (and (is hand!len 5)
       (every [is _!suit hand!car!suit] hand)))

(def straight (hand)
  "Does this hand contain a straight?"
  (withs (ranks  (map #'rank hand)
          scores (map #'convert ranks))
    (and (is hand!len 5)
         (every [is _ 1] (vals (counts scores)))
         (with (smallest (best #'< scores)
                sum (reduce #'+ scores))
           (or (is (+ sum (* smallest -5)) 10)
               (and (mem 'a ranks)
                    (is sum (+ 2 3 4 5 14))))))))

(def ranks-are (hand ranks)
  "Do the ranks in the HAND match the counts in RANKS? If so return a
   'score' which represents how good of a hand this hand is relative to
   hands of the same type."
  (assert (is (reduce #'+ ranks) 5) () "These ranks are not expecting five cards.")
  (ado (map #'rank hand)
       (counts it)
       (tablist it)
       ;; By sorting rank first and then stabily sorting by count, we
       ;; keep elements that occur the same number of times but
       ;; different rank in proper order.
       (sort #'rank> it #'car)
       (ssort #'> it #'cadr)
       (when (or (no ranks)
                 (iso (map #'cadr it)
                      (if (and (is hand!len 3)
                               (iso (lastcons ranks 2) '(1 1)))
                          (butlast ranks 2)
                          ranks)))
         (cars it))))

(mac gen-score-body (hand &rest hands)
  "Generates a code that will become the body of score. For each hand
   return a unique score which we can compare from lexicographically
   to see which is better."
  (w/uniq gvar
    `(hand-match ,gvar ,hand
       ,@(iter (for i downfrom 0)
               (for hand in hands)
               (collect hand)
               (collect `(cons ,i ,gvar))))))

(def score (hand)
  "Return a unique score for a hand which we can compare to see which
   is better."
  (gen-score-body hand
    (t t     1 1 1 1 1)
    (nil nil 4 1)
    (nil nil 3 2)
    (t nil   1 1 1 1 1)
    (nil t   1 1 1 1 1)
    (nil nil 3 1 1)
    (nil nil 2 2 1)
    (nil nil 2 1 1 1)
    (nil nil 1 1 1 1 1)))

(def score< (s1 s2)
  "Is the first score less than the second?"
  (iter (for i in s1)
        (for j in s2)
        (when (~iso i j)
          (return-from score< (values (rank< i j) t))))
  ;; Otherwise the scores are the same.
  (values nil nil))

(def hand> (h1 h2)
  "Is the first hand worse than the second. Return a second value that
   is nil if the hands are equivalent."
  (score< (score h2) (score h1)))

(def shuffle (cards)
  "Shuffles a list of cards."
  (if (no cards)
      '()
      (let next (rand-elt cards)
        (cons next (shuffle (rem next cards))))))

(def make-deck ()
  "Creates a new deck."
  (shuffle
    (accum a
      (each rank ranks*
        (each suit suits*
          (a (make-card rank suit)))))))

(def valid (top middle bottom)
  "Are these hands valid? As in do they not fault."
  (and (hand> middle top)
       (hand> bottom middle)))

(def choose (n xs)
  "Choose N random elements of XS."
  (accum a
    (repeat n
      (let next (rand-elt xs)
        (a next)
        (= xs (rem next xs))))))

(def monte-carlo (top middle bottom n deck)
  "With the given hands, use monte-carlo with clairvoyance to
   determine the probability of not faulting."
  (with (num-cards (- 13 (reduce #'+ (list top middle bottom) :key #'len))
         total 0)
    (repeat n
      (++ total (hands-strength top middle bottom (choose num-cards deck))))
    (/ total n)))

(def legal (top middle bottom n)
  (or (and (is n 1) (len< top 3))
      (and (is n 2) (len< middle 5))
      (and (is n 3) (len< bottom 5))))

(def calc (card top middle bottom n deck)
  "Calculate what the player should do."
  (= deck (rem card deck))
  (withs (state (make-random-state t)
          top-score (let *random-state* (make-random-state state)
                         (monte-carlo (cons card top) middle bottom n deck))
          mid-score (let *random-state* (make-random-state state)
                         (monte-carlo top (cons card middle) bottom n deck))
          bot-score (let *random-state* (make-random-state state)
                         (monte-carlo top middle (cons card bottom) n deck)))
    (withs (legal (keep [legal top middle bottom (car _)]
                        (list (list 1 top-score) (list 2 mid-score) (list 3 bot-score)))
             best (reduce #'max legal :initial-value 0 :key #'cadr)
             choices (keep [is _ best] legal :key #'cadr))
      (if (is (len choices) 2)
          ;; If the card could be put either way, its probably because
          ;; it would suck on top.
          (best #'> (cars choices))
          (car (rand-elt choices))))))

(def safe (top middle bottom cards)
  (if (no cards)
      (valid top middle bottom)
      (or (and (len< top 3)
               (safe (cons (car cards) top)
                     middle
                     bottom
                     (cdr cards)))
          (and (len< middle 5)
               (safe top
                     (cons (car cards) middle)
                     bottom
                     (cdr cards)))
          (and (len< bottom 5)
               (safe top
                     middle
                     (cons (car cards) bottom)
                     (cdr cards))))))

(def hands-strength (top middle bottom cards)
  (if (no cards)
      (raw-hands-strength top middle bottom)
      (max (if (not (len< top 3))
               0
               (hands-strength (cons (car cards) top)
                       middle
                       bottom
                       (cdr cards)))
           (if (not (len< middle 5))
               0
               (hands-strength top
                               (cons (car cards) middle)
                               bottom
                               (cdr cards)))
           (if (not (len< bottom 5))
               0
               (hands-strength top
                               middle
                               (cons (car cards) bottom)
                               (cdr cards))))))

(def raw-hands-strength (top middle bottom)
  (if (not (valid top middle bottom))
      0
      (+ (raw-hand-strength top)
         (raw-hand-strength middle)
         (raw-hand-strength bottom))))

(def raw-hand-strength (hand)
  ;; Using the probability of the hand beating another random hand as
  ;; the raw strength.
  (- 1
     (or (hand-match x hand
           (t t 1 1 1 1 1)     1.539078e-5
           (nil nil 4 1)       2.5548678e-4
           (nil nil 3 2)       0.0016960668
           (t nil 1 1 1 1 1)   0.0036614668
           (nil t 1 1 1 1 1)   0.0075861164
           (nil nil 3 1 1)     0.02871462
           (nil nil 2 2 1)     0.07625362
           (nil nil 2 1 1 1)   0.4988226
           (nil nil 1 1 1 1 1) 0.9999996)
         (error "Hand not matched."))))

(def parse-card (string)
  (let val (nth-value 1 (scan-to-strings "^(\\d0?)(.)$" string))
       (if val
           (list (parse-integer (string val.0)) (intern (upcase val.1)))
           (list (intern (upcase (string string.0)))
                 (intern (upcase (string string.1)))))))

;; (def play ()
;;   (with (deck (make-deck)
;;          num (parse-integer (read-line))
;;          top '()
;;          mid '()
;;          bot '())
;;     (repeat (dec num)
;;       (= deck (set-difference deck (map #'parse-card (tokens (read-line))) :test #'iso))
;;       (read-line))
;;     (each card (map #'parse-card (tokens (read-line)))
;;       (= deck (rem card deck))
;;       (case (calc card top mid bot 100 deck)
;;         1 (do (push card top) (pr 1 " "))
;;         2 (do (push card mid) (pr 2 " "))
;;         3 (do (push card bot) (pr 3 " "))))
;;     (prn)
;;     (force-output)
;;     (repeat 8
;;       (repeat 2
;;         (= deck (set-difference deck (map #'parse-card (tokens (read-line))) :test #'iso))
;;         (read-line))
;;       (let card (parse-card (car (tokens (read-line))))
;;         (case (calc card top mid bot 1000 deck)
;;           1 (do (push card top) (prn 1))
;;           2 (do (push card mid) (prn 2))
;;           3 (do (push card bot) (prn 3)))
;;         (force-output)))
;;     (repeat (- 3 num)
;;       (repeat 2
;;         (read-line)))
;;     (repeat 4
;;       (read-line))))

(mac gen-heurstic-body (hand &rest pats)
  (w/uniq (gvar gcard galist)
    (once-only (hand)
      `(hand-almost-match ,gvar ,hand
         ,@(iter (for (pattern placement) on pats by #'cddr)
                 (collect pattern)
                 (collect `(let ,galist (map #'list ,gvar ',placement)
                             (mapeach ,gcard ,hand
                               (cadr (find ,gcard ,galist :key #'car))))))))))

(mac hand-almost-match (var hand &body clauses)
  "Does the hand satisify one of the hand patterns."
  (once-only (hand)
    `(iflet ,var
       ,@(mappendeach ((type data) body) (group clauses :by 2)
           `((hand-almost-is ,type ',data ,hand) ,body)))))

(defmethod hand-almost-is ((type (eql :flush)) n hand)
  (each suit suits*
    (when (>= (count suit hand :key #'suit) n)
      (mvb (same diff) (partition suit hand :key #'suit)
        (return-from hand-almost-is (append (sort #'rank> same #'rank)
                                            (sort #'rank> diff #'rank)))))))

(defmethod hand-almost-is ((type (eql :straight)) n hand)
  (iter (with ranks = (redup (map #'rank hand)))
        (for (a b c d e) on (append ranks* '(a)))
        (while e)
        (let int (intersection (list a b c d e) ranks)
          (when (>= (len int) n)
            (let partial-straight (mapeach rank int
                                    (find rank hand :key #'rank))
              (return (append (sort #'rank> partial-straight #'rank)
                              (sort #'rank> (set-difference hand partial-straight) #'rank))))))))

(defmethod hand-almost-is ((type (eql :ranks)) ranks hand)
  (awhen (ranks-are hand ranks)
    (iter (for rank in it)
          (appending (keep rank hand :key #'rank)))))

(def heuristic (hand)
  "Determine the heuristic to apply for this hand."
  (gen-heurstic-body hand
    (:ranks (4 1)) (3 3 3 3 2)
    (:ranks (3 2)) (3 3 3 3 3)
    (:flush 5) (3 3 3 3 3)
    (:straight 5) (3 3 3 3 3)
    (:flush 4) (3 3 3 3 2)
    (:straight 4) (3 3 3 3 2)
    (:ranks (3 1 1)) (3 3 3 2 1)
    (:ranks (2 2 1)) (3 3 3 3 2)
    (:ranks (2 1 1 1)) (3 3 2 2 1)
    (:ranks (1 1 1 1 1)) (3 3 2 2 1)))

(def play ()
  (with (deck (make-deck)
         num (parse-integer (read-line))
         top '()
         mid '()
         bot '())
    (repeat (dec num)
      (= deck (set-difference deck (map #'parse-card (tokens (read-line))) :test #'iso))
      (read-line))
    (let cards (map #'parse-card (tokens (read-line)))
      (let moves (heuristic cards)
        (prf "~{~A~^ ~}~%" moves)
        (force-output)
        (= deck (set-difference deck cards :test #'iso))
        (iter (for card in cards)
              (for move in moves)
              (case move
                1 (push card top)
                2 (push card mid)
                3 (push card bot)))))
    (repeat 8
      (repeat 2
        (= deck (set-difference deck (map #'parse-card (tokens (read-line))) :test #'iso))
        (read-line))
      (let card (parse-card (car (tokens (read-line))))
        (case (calc card top mid bot 100 deck)
          1 (do (push card top) (prn 1))
          2 (do (push card mid) (prn 2))
          3 (do (push card bot) (prn 3)))
        (force-output)))
    (repeat (- 3 num)
      (repeat 2
        (read-line)))
    (repeat 3
      (read-line))
    (let val (parse-integer (elt (ret x (nth-value 1 (scan-to-strings "^(-?\\d+) (-?\\d+) (-?\\d+)$" (read-line)))
                                   (push x vals*)) (dec num)))
      (++ score* val))
    nil))

(defvar vals* nil)

;; (play)

(defparameter score* 0)

(defmacro w/socket ((var &rest options) &body body)
  `(let ,var (usocket:socket-connect ,@options)
     (unwind-protect (do ,@body)
       (usocket:socket-close ,var))))



(def play-game-with-sockets ()
  (w/socket (socket "games.recurse.com" 10000)
    (with (*standard-input* (usocket:socket-stream socket)
           *standard-output* (usocket:socket-stream socket))
      (play))))
