Imgload: module {
	PATH: con "/dis/xenith/imgload.dis";

	init: fn(d: ref Draw->Display);
	readimage: fn(path: string): (ref Draw->Image, string);
	readimagedata: fn(data: array of byte, hint: string): (ref Draw->Image, string);
};
