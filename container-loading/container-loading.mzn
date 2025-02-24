%% Problem Description
% Given a container of fixed length, width and height. Packages shaped like 3-dimensional boxes
% are to be placed in the container such that none overlap and their area is minmized. The area is calculated
% by multiplying the length, width and height of the placed packages. Rotations of the packages and the 
% container is not allowed.
%
%            +--------------+
%           /|             /|
%          / |            / |
%         *--+-----------*  |
%         |  |           |  |
% height->|  |           |  |
%         |  |           |  |
%         |  +-----------+--+
%         | / <-width    | /
%         |/             |/
%         *--------------*
%             length^

include "diffn_k.mzn";
%% Parameters
int: container_length; 
int: container_width;
int: container_height;
int: n; % Total number of boxes
array[1..n, 1..4] of int: boxes; % Boxes to be placed in the with length, width, heigth and number of each box

%% Derived Parameters
% Total number of boxes
int: total_boxes = sum(boxes[..,4]); 
% All box sizes
array[1..total_boxes, 1..3] of int: box_sizes = array2d(1..total_boxes, 1..3, 
    [
        [boxes[i,1], boxes[i,2],boxes[i,3]][x] 
        | i in 1..n, _ in 1..boxes[i,4], x in 1..3
    ]);

%% Descision Variables
% Starting positions of all boxes
array[1..total_boxes, 1..3] of var 1..max([container_length, container_width, container_height]): start_pos::add_to_output;
% The length of the placed boxes
var 1..container_length: l::add_to_output = max(i in 1..total_boxes) (start_pos[i,1] + box_sizes[i,1]);
% The width of the placed boxes
var 1..container_width:  w::add_to_output = max(i in 1..total_boxes) (start_pos[i,2] + box_sizes[i,2]);
% The height of the placed boxes
var 1..container_height: h::add_to_output = max(i in 1..total_boxes) (start_pos[i,3] + box_sizes[i,3]);

%% Constraints
% None of the boxes can be overlapping
constraint diffn_k(start_pos, box_sizes);

% The boxes are to be placed such that they are within the limits of the container
constraint forall(i in 1..total_boxes) 
    (
        start_pos[i, 1] + box_sizes[i, 1] <= container_length + 1 /\
        start_pos[i, 2] + box_sizes[i, 2] <= container_width + 1  /\
        start_pos[i, 3] + box_sizes[i, 3] <= container_height + 1
    );

solve minimize l*w*h;
