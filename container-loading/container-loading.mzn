include "diffn_k.mzn";
%% Parameters
int: container_length;
int: container_width;
int: container_height;
int: n; % Total number of boxes
array[1..n, 1..4] of int: boxes;


int: no_boxes = sum(boxes[..,4]);

array[1..no_boxes] of int: box_sizesX = 
    [boxes[i, 1] | i in 1..n, _ in 1..boxes[i,4]];

array[1..no_boxes] of int: box_sizesY = 
    [boxes[i, 2] | i in 1..n, _ in 1..boxes[i,4]];

array[1..no_boxes] of int: box_sizesZ = 
    [boxes[i, 3] | i in 1..n, _ in 1..boxes[i,4]];


    

%% Descision Variables

array[1..no_boxes, 1..3] of var min(boxes[..,1..3])..max(boxes[..,1..3]): box_sizes::add_to_output;

array[1..no_boxes, 1..3] of var 1..max([container_length, container_width, container_height]): startXYZ::add_to_output;

var 1..no_boxes*sum(boxes[..,1]): l::add_to_output = max(i in 1..no_boxes) (startXYZ[i,1] + box_sizes[i,1]);
var 1..no_boxes*sum(boxes[..,2]): w::add_to_output = max(i in 1..no_boxes) (startXYZ[i,2] + box_sizes[i,2]);
var 1..no_boxes*sum(boxes[..,3]): h::add_to_output = max(i in 1..no_boxes) (startXYZ[i,3] + box_sizes[i,3]);

constraint forall(i in 1..no_boxes) 
    (
        box_sizes[i,1] = box_sizesX[i] /\
        box_sizes[i,2] = box_sizesY[i] /\ 
        box_sizes[i,3] = box_sizesZ[i] 
    );

constraint diffn_k(startXYZ, box_sizes);

constraint forall(i in 1..no_boxes) 
    (
        startXYZ[i, 1] + box_sizes[i, 1] <= container_length /\
        startXYZ[i, 1] >= 0
    );
constraint forall(i in 1..no_boxes) 
    (
        startXYZ[i, 2] + box_sizes[i, 2] <= container_width /\
        startXYZ[i, 2] >= 0
    );
constraint forall(i in 1..no_boxes) 
    (
        startXYZ[i, 3] + box_sizes[i, 3] <= container_height /\
        startXYZ[i, 3] >= 0
    );

solve minimize l*w*h;


