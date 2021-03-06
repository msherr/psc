// Code generated by protoc-gen-go.
// source: dpres.proto
// DO NOT EDIT!

/*
Package DPres is a generated protocol buffer package.

It is generated from these files:
	dpres.proto

It has these top-level messages:
	Response
*/
package DPres

import proto "github.com/golang/protobuf/proto"
import fmt "fmt"
import math "math"

// Reference imports to suppress errors if they are not otherwise used.
var _ = proto.Marshal
var _ = fmt.Errorf
var _ = math.Inf

// This is a compile-time assertion to ensure that this generated file
// is compatible with the proto package it is being compiled against.
// A compilation error at this line likely means your copy of the
// proto package needs to be updated.
const _ = proto.ProtoPackageIsVersion2 // please upgrade the proto package

type Response struct {
	K                [][]byte `protobuf:"bytes,1,rep,name=K" json:"K,omitempty"`
	C                [][]byte `protobuf:"bytes,2,rep,name=C" json:"C,omitempty"`
	XXX_unrecognized []byte   `json:"-"`
}

func (m *Response) Reset()                    { *m = Response{} }
func (m *Response) String() string            { return proto.CompactTextString(m) }
func (*Response) ProtoMessage()               {}
func (*Response) Descriptor() ([]byte, []int) { return fileDescriptor0, []int{0} }

func (m *Response) GetK() [][]byte {
	if m != nil {
		return m.K
	}
	return nil
}

func (m *Response) GetC() [][]byte {
	if m != nil {
		return m.C
	}
	return nil
}

func init() {
	proto.RegisterType((*Response)(nil), "DPres.Response")
}

func init() { proto.RegisterFile("dpres.proto", fileDescriptor0) }

var fileDescriptor0 = []byte{
	// 78 bytes of a gzipped FileDescriptorProto
	0x1f, 0x8b, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x02, 0xff, 0xe2, 0xe2, 0x4e, 0x29, 0x28, 0x4a,
	0x2d, 0xd6, 0x2b, 0x28, 0xca, 0x2f, 0xc9, 0x17, 0x62, 0x75, 0x09, 0x28, 0x4a, 0x2d, 0x56, 0x52,
	0xe3, 0xe2, 0x08, 0x4a, 0x2d, 0x2e, 0xc8, 0xcf, 0x2b, 0x4e, 0x15, 0xe2, 0xe1, 0x62, 0xf4, 0x96,
	0x60, 0x54, 0x60, 0xd6, 0xe0, 0x09, 0x62, 0xf4, 0x06, 0xf1, 0x9c, 0x25, 0x98, 0x20, 0x3c, 0x67,
	0x40, 0x00, 0x00, 0x00, 0xff, 0xff, 0x8c, 0x8e, 0xe2, 0xfe, 0x3c, 0x00, 0x00, 0x00,
}
