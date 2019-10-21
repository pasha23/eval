eval.list: eval
	objdump -C -S eval > eval.list

eval: eval.cpp
	g++ -std=c++17 -ggdb3 -O1 -o eval eval.cpp -lunwind
#	g++ -std=c++17 -ggdb3 -O3 -o eval eval.cpp -lunwind

