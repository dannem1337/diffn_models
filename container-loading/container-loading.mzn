include "diffn_k.mzn";
%% Parameters
int: n; % Total number of boxes
array[1..n, 1..4] of int: boxes;


int: no_boxes = sum(boxes[..,4]);

array[1..no_boxes] of int: box_sizesX = 
    [boxes[i, 1] | i in 1..n, _ in 1..boxes[i,4]];

array[1..no_boxes] of int: box_sizesY = 
    [boxes[i, 2] | i in 1..n, _ in 1..boxes[i,4]];

array[1..no_boxes] of int: box_sizesZ = 
    [boxes[i, 3] | i in 1..n, _ in 1..boxes[i,4]];


    

%% Decsision Variables

array[1..no_boxes, 1..3] of var int: box_sizes::add_to_output;

array[1..no_boxes, 1..3] of var int: startXYZ::add_to_output;

var int: l::add_to_output = max(i in 1..no_boxes) (startXYZ[i,1] + box_sizes[i,1]);
var int: w::add_to_output = max(i in 1..no_boxes) (startXYZ[i,2] + box_sizes[i,2]);
var int: h::add_to_output = max(i in 1..no_boxes) (startXYZ[i,3] + box_sizes[i,3]);
var int: area::add_to_output = l*w*h;



constraint forall(i in 1..no_boxes) 
    (
        box_sizes[i,1] = box_sizesX[i] /\
        box_sizes[i,2] = box_sizesY[i] /\ 
        box_sizes[i,3] = box_sizesZ[i] 
    );

constraint diffn_k(startXYZ, box_sizes);

constraint forall(i in 1..no_boxes) (
                startXYZ[i, 1] > 0 /\
                startXYZ[i, 2] > 0 /\
                startXYZ[i, 3] > 0
                );
solve minimize area;


