(* funkcja symulujaca wylewanie wody ze szklanki *)
(* q to kolejka osiagnietych do tej pory stanow napelnienia szklanek *)
(* arr to tablica odpowiadajaca przerabianemu stanowi *)
(* size to ilosc szklanek *)
(* limit to tablica z pojemnosciami szklanek *)
(* visit to mapa odwiedzonych stanow *)
(* moves to minimalna ilosc ruchow potrzebnych do osiagniecia danego stanu *)
let empty q arr size limit visit moves =
	for i = 0 to size - 1 do
		if arr.(i) = limit.(i) then
			let new_arr = Array.copy arr in
			begin
				new_arr.(i) <- 0;
				if Hashtbl.mem visit new_arr = false then
					begin
						Queue.push (new_arr, moves + 1) q;
						Hashtbl.add visit new_arr true
					end
			end
	done;
	q

(* funkcja symulujaca nalewanie wody do szklanki do pelna *)
(* zmienne takie same jak w funkcji empty *)
let full q arr size limit visit moves =
	for i = 0 to size - 1 do
		if arr.(i) = 0 then
			let new_arr = Array.copy arr in
			begin
				new_arr.(i) <- limit.(i);
				if Hashtbl.mem visit new_arr = false then
					begin
						Queue.push (new_arr, moves + 1) q;
						Hashtbl.add visit new_arr true
					end
			end
	done;
	q

(* funkcja symulujaca przelewanie wody z jednej szklanki do drugiej *)
(* zmienne takie same jak w funkcji empty *)
let decanting q arr size limit visit moves =
	for i = 0 to size - 1 do
		for j = 0 to size - 1 do
			if i <> j && arr.(i) <> 0 && arr.(j) <> limit.(j) then
				let new_arr = Array.copy arr in
				let transfer = min arr.(i) (limit.(j) - arr.(j)) in
				begin
					new_arr.(i) <- new_arr.(i) - transfer;
					new_arr.(j) <- new_arr.(j) + transfer;
					if Hashtbl.mem visit new_arr = false then
					begin
						Queue.push (new_arr, moves + 1) q;
						Hashtbl.add visit new_arr true
					end
				end
		done
	done;
	q

(* funkcja wykonujaca przeszukiwanie wszerz po stanach napelnienia szklanek *)
(* out - tablica reprezentujaca koncowy stan *)
(* reszta tak jak w funkcji empty *)
let rec bfs q size limit visit out =
	if Queue.is_empty q then -1
	else
		let (arr, moves) = Queue.pop q in
		if arr = out then moves
		else
			let q = decanting q arr size limit visit moves in
			let q = full q arr size limit visit moves in
			let q = empty q arr size limit visit moves in
			bfs q size limit visit out

(* funkcja sprawdzajaca, czy mozliwe jest uzyskanie 
koncowego stanu napelnienia szklanek *)
(* arr to tablica opisujaca koncowy stan *)
let nwd arr =
	let rec nwd_of_two a b =
		if a = 0 then b else nwd_of_two (b mod a) a
	in
	let nwd_of_all = Array.fold_left (fun acc (a, _) -> 
		if a <> 0 then nwd_of_two (min acc a) (max acc a) else acc) 0 arr
	in
	let ok = Array.fold_left (fun acc (_, b) ->
		if b mod nwd_of_all = 0 then acc else false) true arr
	in
	if ok then true
	else false

(* funkcja wykorzystujaca nwd do sprawdzenia, czy mozna 
uzyskac koncowy stan napelnienia szklanek *)
(* koncowy stan opisuje tablica arr *)
let ans_exist arr =
	let count = Array.fold_left (fun acc (a, b) ->
		if a <> 0 && (b = 0 || b = a) then acc + 1 else acc) 0 arr
	in
	if count > 0 then nwd arr
	else false

(* glowna funkcja liczaca minimalna liczbe ruchow by osiagnac 
stan koncowy napelnienia szklanek opisany przez tablice in_arr *)
(* za pomoca funkcji ans_exist sprawdzamy mozliwosc osiagniecia 
ostatecznego stanu *)
(* useless - ilosc szkanek o pojenosci 0 *)
(* zeros - ilosc szklanek, ktore ostatecznie maja miec poziom wody 0 *)
(* visit - mapa odwiedzonych stanow *)
(* limit - tablica maksymalnej pojemnosci szklanek *)
(* out - tablica opisujaca, jak ma wygladac ostatni stan *)
let przelewanka in_arr =
	let n = Array.length in_arr in
	let useless = Array.fold_left
		(fun acc (a, _) -> if a = 0 then acc + 1 else acc) 0 in_arr in
	if n - useless > 0 && ans_exist in_arr = false then (-1)
	else
		let check = Array.fold_left 
			(fun acc (a, b) -> if a = b then acc else 0) 1 in_arr in
		let zeros = Array.fold_left
			(fun acc (_, b) -> if b = 0 then acc + 1 else acc) 0 in_arr in
		if check = 1 then n - zeros
		else
			let arr = Array.make n 0 in
			let visit = Hashtbl.create 100000 in
			let q = Queue.create () in
			let limit = Array.init n (fun i -> fst in_arr.(i)) in
			let out = Array.init n (fun i -> snd in_arr.(i)) in
			begin
				Hashtbl.add visit arr true;
				Queue.push (arr, 0) q;
				bfs q n limit visit out
			end

(* TESTY *)
(* assert (przelewanka [| (10,2); (1,1) |] = 5);;
assert (przelewanka [| (0,0); (2,2); (2,2); (2,2); (0,0); (0,0); (1,0);
  (0,0); (1,0) |] = (3));;
assert (przelewanka [| (1,1); (2,1); (3,0); (4,2) |] = (3));;
assert (przelewanka [| (0,0); (2,2); (1,0); (1,1); (1,0); (2,2); (1,0);
  (0,0); (0,0) |] = (3));;
assert (przelewanka [| (11,11); (11,1) |] = (-1));;
assert (przelewanka [| (1,1); (0,0); (2,2); (0,0); (2,0); (0,0); (0,0);
  (1,0); (2,0); (1,0) |] = (2));;
assert (przelewanka [| (5,2); (0,0); (0,0); (2,0); (3,2) |] = (4));;
assert (przelewanka [| (1,1); (0,0); (4,4); (4,0); (4,4) |] = (3));;
assert (przelewanka [| (9,9); (13,12) |] = (10));;
assert (przelewanka [| (2,2); (1,0); (2,2); (0,0); (1,0); (0,0); (1,1);
  (1,0); (0,0) |] = (3));;
assert (przelewanka [| (5,2); (3,1); (0,0); (4,1); (0,0); (1,0) |] = (5));;
assert (przelewanka [| (310,76); (139,91) |] = (-1));;
assert (przelewanka [| (48,9); (12,0); (1,1); (65,64) |] = (10));;
assert (przelewanka [| (7,5); (3,3); (9,4); (10,4); (6,3); (5,3) |] =
  (8));;
assert (przelewanka [| (100000,50000); (1,1) |] = (100000));;
assert (przelewanka [| (0,0); (0,0); (0,0); (300000,151515);
  (1,0); (0,0) |] = (296971));;
assert (przelewanka [| (11,2); (11,10); (4,0); (10,8); (21,16) |] = (12));;
assert (przelewanka [| (50,1); (7,3); (78,64) |] = (-1));;
assert (przelewanka [| (85,23); (524,210) |] = (-1));;
assert (przelewanka [| (557,349); (73,49) |] = (-1));;
assert (przelewanka [| (62,3); (38,7) |] = (-1));;
assert (przelewanka [| (15,15); (6,3); (42,32); (33,20) |] = (-1));;
assert (przelewanka [| (39,12); (35,34); (21,7); (2,1) |] = (-1));;
assert (przelewanka [| (1,0); (2,1); (2,1); (0,0); (2,0); (0,0); (0,0);
  (0,0); (1,1); (0,0); (1,0) |] = (4));;
assert (przelewanka [| (2,0); (2,2); (2,1); (6,6); (0,0) |] = (-1));;
assert (przelewanka [| (2,0); (1,1); (1,1); (1,1); (0,0); (1,0); (3,2);
  (0,0) |] = (4));;
assert (przelewanka [| (1,1); (2,2); (4,1); (0,0); (1,0); (2,1) |] = (5));;
assert (przelewanka [| (1,0); (3,1); (2,2); (1,1); (1,0); (1,0) |] = (3));;
assert (przelewanka [| (20,7); (12,11) |] = (-1));;
assert (przelewanka [| (0,0); (21,21) |] = (1));;
assert (przelewanka [| (13,8); (11,11) |] = (14));;
assert (przelewanka [| (1,1); (3,2); (6,5) |] = (5));;
assert (przelewanka [| (4,4); (7,6); (2,2) |] = (6));;
assert (przelewanka [| (3,2); (3,3); (1,1); (2,0) |] = (3));;
assert (przelewanka [| (0,0); (2,0); (0,0); (2,0); (3,2); (2,1); (1,0) |] =
  (3));; *)