eval.list: eval
	objdump -C -S eval > eval.list

eval: eval.cpp
	g++ -std=c++17 -ggdb3 -o eval eval.cpp -lunwind

