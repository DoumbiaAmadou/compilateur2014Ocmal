def compose f g = { x -> f (g x) }
def plus x y = x + y
val deux = 2
val res = compose { x -> deux * x } (plus 1) 3
/* answer : 8 */