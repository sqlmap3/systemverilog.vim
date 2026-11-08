class demo59;
int arr[10];
int q[$];
string s;
function void run();
int total;
int min_v;
int max_v;
total = arr.sum();
min_v = arr.min();
max_v = arr.max();
arr.sort();
arr.shuffle();
q.push_back(1);
q.push_front(2);
q.pop_back();
q.pop_front();
q.insert(0, 5);
q.delete(1);
s = "hello";
$display("%0d", s.len());
$display("%s", s.substr(1, 3));
$display("%0d", s.atoi());
s = s.tolower();
endfunction
endclass
