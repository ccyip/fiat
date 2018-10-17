# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: conformance.proto

import sys
_b=sys.version_info[0]<3 and (lambda x:x) or (lambda x:x.encode('latin1'))
from google.protobuf.internal import enum_type_wrapper
from google.protobuf import descriptor as _descriptor
from google.protobuf import message as _message
from google.protobuf import reflection as _reflection
from google.protobuf import symbol_database as _symbol_database
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()




DESCRIPTOR = _descriptor.FileDescriptor(
  name='conformance.proto',
  package='conformance',
  syntax='proto3',
  serialized_options=_b('\n\037com.google.protobuf.conformance'),
  serialized_pb=_b('\n\x11\x63onformance.proto\x12\x0b\x63onformance\"\xa3\x01\n\x12\x43onformanceRequest\x12\x1a\n\x10protobuf_payload\x18\x01 \x01(\x0cH\x00\x12\x16\n\x0cjson_payload\x18\x02 \x01(\tH\x00\x12\x38\n\x17requested_output_format\x18\x03 \x01(\x0e\x32\x17.conformance.WireFormat\x12\x14\n\x0cmessage_type\x18\x04 \x01(\tB\t\n\x07payload\"\xb1\x01\n\x13\x43onformanceResponse\x12\x15\n\x0bparse_error\x18\x01 \x01(\tH\x00\x12\x19\n\x0fserialize_error\x18\x06 \x01(\tH\x00\x12\x17\n\rruntime_error\x18\x02 \x01(\tH\x00\x12\x1a\n\x10protobuf_payload\x18\x03 \x01(\x0cH\x00\x12\x16\n\x0cjson_payload\x18\x04 \x01(\tH\x00\x12\x11\n\x07skipped\x18\x05 \x01(\tH\x00\x42\x08\n\x06result*5\n\nWireFormat\x12\x0f\n\x0bUNSPECIFIED\x10\x00\x12\x0c\n\x08PROTOBUF\x10\x01\x12\x08\n\x04JSON\x10\x02\x42!\n\x1f\x63om.google.protobuf.conformanceb\x06proto3')
)

_WIREFORMAT = _descriptor.EnumDescriptor(
  name='WireFormat',
  full_name='conformance.WireFormat',
  filename=None,
  file=DESCRIPTOR,
  values=[
    _descriptor.EnumValueDescriptor(
      name='UNSPECIFIED', index=0, number=0,
      serialized_options=None,
      type=None),
    _descriptor.EnumValueDescriptor(
      name='PROTOBUF', index=1, number=1,
      serialized_options=None,
      type=None),
    _descriptor.EnumValueDescriptor(
      name='JSON', index=2, number=2,
      serialized_options=None,
      type=None),
  ],
  containing_type=None,
  serialized_options=None,
  serialized_start=380,
  serialized_end=433,
)
_sym_db.RegisterEnumDescriptor(_WIREFORMAT)

WireFormat = enum_type_wrapper.EnumTypeWrapper(_WIREFORMAT)
UNSPECIFIED = 0
PROTOBUF = 1
JSON = 2



_CONFORMANCEREQUEST = _descriptor.Descriptor(
  name='ConformanceRequest',
  full_name='conformance.ConformanceRequest',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='protobuf_payload', full_name='conformance.ConformanceRequest.protobuf_payload', index=0,
      number=1, type=12, cpp_type=9, label=1,
      has_default_value=False, default_value=_b(""),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='json_payload', full_name='conformance.ConformanceRequest.json_payload', index=1,
      number=2, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='requested_output_format', full_name='conformance.ConformanceRequest.requested_output_format', index=2,
      number=3, type=14, cpp_type=8, label=1,
      has_default_value=False, default_value=0,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='message_type', full_name='conformance.ConformanceRequest.message_type', index=3,
      number=4, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
  ],
  extensions=[
  ],
  nested_types=[],
  enum_types=[
  ],
  serialized_options=None,
  is_extendable=False,
  syntax='proto3',
  extension_ranges=[],
  oneofs=[
    _descriptor.OneofDescriptor(
      name='payload', full_name='conformance.ConformanceRequest.payload',
      index=0, containing_type=None, fields=[]),
  ],
  serialized_start=35,
  serialized_end=198,
)


_CONFORMANCERESPONSE = _descriptor.Descriptor(
  name='ConformanceResponse',
  full_name='conformance.ConformanceResponse',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='parse_error', full_name='conformance.ConformanceResponse.parse_error', index=0,
      number=1, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='serialize_error', full_name='conformance.ConformanceResponse.serialize_error', index=1,
      number=6, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='runtime_error', full_name='conformance.ConformanceResponse.runtime_error', index=2,
      number=2, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='protobuf_payload', full_name='conformance.ConformanceResponse.protobuf_payload', index=3,
      number=3, type=12, cpp_type=9, label=1,
      has_default_value=False, default_value=_b(""),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='json_payload', full_name='conformance.ConformanceResponse.json_payload', index=4,
      number=4, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
    _descriptor.FieldDescriptor(
      name='skipped', full_name='conformance.ConformanceResponse.skipped', index=5,
      number=5, type=9, cpp_type=9, label=1,
      has_default_value=False, default_value=_b("").decode('utf-8'),
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      serialized_options=None, file=DESCRIPTOR),
  ],
  extensions=[
  ],
  nested_types=[],
  enum_types=[
  ],
  serialized_options=None,
  is_extendable=False,
  syntax='proto3',
  extension_ranges=[],
  oneofs=[
    _descriptor.OneofDescriptor(
      name='result', full_name='conformance.ConformanceResponse.result',
      index=0, containing_type=None, fields=[]),
  ],
  serialized_start=201,
  serialized_end=378,
)

_CONFORMANCEREQUEST.fields_by_name['requested_output_format'].enum_type = _WIREFORMAT
_CONFORMANCEREQUEST.oneofs_by_name['payload'].fields.append(
  _CONFORMANCEREQUEST.fields_by_name['protobuf_payload'])
_CONFORMANCEREQUEST.fields_by_name['protobuf_payload'].containing_oneof = _CONFORMANCEREQUEST.oneofs_by_name['payload']
_CONFORMANCEREQUEST.oneofs_by_name['payload'].fields.append(
  _CONFORMANCEREQUEST.fields_by_name['json_payload'])
_CONFORMANCEREQUEST.fields_by_name['json_payload'].containing_oneof = _CONFORMANCEREQUEST.oneofs_by_name['payload']
_CONFORMANCERESPONSE.oneofs_by_name['result'].fields.append(
  _CONFORMANCERESPONSE.fields_by_name['parse_error'])
_CONFORMANCERESPONSE.fields_by_name['parse_error'].containing_oneof = _CONFORMANCERESPONSE.oneofs_by_name['result']
_CONFORMANCERESPONSE.oneofs_by_name['result'].fields.append(
  _CONFORMANCERESPONSE.fields_by_name['serialize_error'])
_CONFORMANCERESPONSE.fields_by_name['serialize_error'].containing_oneof = _CONFORMANCERESPONSE.oneofs_by_name['result']
_CONFORMANCERESPONSE.oneofs_by_name['result'].fields.append(
  _CONFORMANCERESPONSE.fields_by_name['runtime_error'])
_CONFORMANCERESPONSE.fields_by_name['runtime_error'].containing_oneof = _CONFORMANCERESPONSE.oneofs_by_name['result']
_CONFORMANCERESPONSE.oneofs_by_name['result'].fields.append(
  _CONFORMANCERESPONSE.fields_by_name['protobuf_payload'])
_CONFORMANCERESPONSE.fields_by_name['protobuf_payload'].containing_oneof = _CONFORMANCERESPONSE.oneofs_by_name['result']
_CONFORMANCERESPONSE.oneofs_by_name['result'].fields.append(
  _CONFORMANCERESPONSE.fields_by_name['json_payload'])
_CONFORMANCERESPONSE.fields_by_name['json_payload'].containing_oneof = _CONFORMANCERESPONSE.oneofs_by_name['result']
_CONFORMANCERESPONSE.oneofs_by_name['result'].fields.append(
  _CONFORMANCERESPONSE.fields_by_name['skipped'])
_CONFORMANCERESPONSE.fields_by_name['skipped'].containing_oneof = _CONFORMANCERESPONSE.oneofs_by_name['result']
DESCRIPTOR.message_types_by_name['ConformanceRequest'] = _CONFORMANCEREQUEST
DESCRIPTOR.message_types_by_name['ConformanceResponse'] = _CONFORMANCERESPONSE
DESCRIPTOR.enum_types_by_name['WireFormat'] = _WIREFORMAT
_sym_db.RegisterFileDescriptor(DESCRIPTOR)

ConformanceRequest = _reflection.GeneratedProtocolMessageType('ConformanceRequest', (_message.Message,), dict(
  DESCRIPTOR = _CONFORMANCEREQUEST,
  __module__ = 'conformance_pb2'
  # @@protoc_insertion_point(class_scope:conformance.ConformanceRequest)
  ))
_sym_db.RegisterMessage(ConformanceRequest)

ConformanceResponse = _reflection.GeneratedProtocolMessageType('ConformanceResponse', (_message.Message,), dict(
  DESCRIPTOR = _CONFORMANCERESPONSE,
  __module__ = 'conformance_pb2'
  # @@protoc_insertion_point(class_scope:conformance.ConformanceResponse)
  ))
_sym_db.RegisterMessage(ConformanceResponse)


DESCRIPTOR._options = None
# @@protoc_insertion_point(module_scope)