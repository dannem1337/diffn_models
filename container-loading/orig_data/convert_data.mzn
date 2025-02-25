
%% Parameters
int: container_length;
int: container_width;
int: container_height;
int: n; % Total number of boxes
array[1..n, 1..4] of int: boxes; % Boxes to be placed in the with length, width, heigth and number of each box

% Workaround for bug in MiniZinc 2.9.0
function int: enum2int($$E: e) = e;

enum Dimension = {Length, Width, Height};
array[Dimension] of int: container_size= [container_length, container_width, container_height];
enum Box ::output = B(1..n);
array[Box] of int: no_boxes = [B(i): boxes[i, 4] | i in 1..n];
array[Box, Dimension] of int: box_size = [(B(i), d): boxes[i, enum2int(d)] | i in 1..n, d in Dimension];

output[
	"container_size = \(container_size);\n",
	"Box = B(1..\(n));\n",
	"no_boxes = \(no_boxes);\n",
	"box_size =\n", show2d(box_size), ";\n",
]
