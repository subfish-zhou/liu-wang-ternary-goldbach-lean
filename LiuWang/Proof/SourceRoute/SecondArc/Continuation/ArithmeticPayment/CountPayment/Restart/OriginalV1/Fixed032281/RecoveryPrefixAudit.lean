import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.EulerConstant
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Constants
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.ConcretePartition
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.DirectedExp
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.CellCertificate
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.CellZero
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.CellData
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block0
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block5
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block6
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block7
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block2
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block1
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block4
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Block3
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Budget
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.RefinedCertificate
import LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281.Refined0

namespace LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281

#check log_correction_lower
#print axioms log_correction_lower
#check correctedEuler
#print axioms correctedEuler
#check correctedEuler_antitone
#print axioms correctedEuler_antitone
#check euler_le_correctedEuler
#print axioms euler_le_correctedEuler
#check euler_upper
#print axioms euler_upper
#check exp_euler_upper
#print axioms exp_euler_upper
#check exp_phase_upper
#print axioms exp_phase_upper
#check log_31_32_bounds
#print axioms log_31_32_bounds
#check log_3100_interval
#print axioms log_3100_interval
#check window_H_lower
#print axioms window_H_lower
#check loglog_interval
#print axioms loglog_interval
#check sourceNu_fixed_upper
#print axioms sourceNu_fixed_upper
#check lower_endpoint
#print axioms lower_endpoint
#check upper_endpoint
#print axioms upper_endpoint
#check fixedPoint
#print axioms fixedPoint
#check fixedMidpoint
#print axioms fixedMidpoint
#check fixedPoint_monotone
#print axioms fixedPoint_monotone
#check fixed_partition_bound
#print axioms fixed_partition_bound
#check roundDown
#print axioms roundDown
#check roundUp
#print axioms roundUp
#check roundDown_le
#print axioms roundDown_le
#check le_roundUp
#print axioms le_roundUp
#check expSeries
#print axioms expSeries
#check expError
#print axioms expError
#check expBaseLower
#print axioms expBaseLower
#check expBaseUpper
#print axioms expBaseUpper
#check expLower
#print axioms expLower
#check expUpper
#print axioms expUpper
#check exp_bounds
#print axioms exp_bounds
#check expLower_nonneg
#print axioms expLower_nonneg
#check mul_exp_upper
#print axioms mul_exp_upper
#check mul_exp_lower
#print axioms mul_exp_lower
#check primitiveCoefficient
#print axioms primitiveCoefficient
#check primitive_factor
#print axioms primitive_factor
#check primitiveAmplitude
#print axioms primitiveAmplitude
#check zeroAmplitude
#print axioms zeroAmplitude
#check cellUpper
#print axioms cellUpper
#check cellValue_le_cellUpper
#print axioms cellValue_le_cellUpper
#check phase_certificate_domain
#print axioms phase_certificate_domain
#check fixedCellUpper
#print axioms fixedCellUpper
#check fixedCell_bound
#print axioms fixedCell_bound
#check fixed_rational_reduction
#print axioms fixed_rational_reduction
#check cell_zero_bound
#print axioms cell_zero_bound
#check cell_0
#print axioms cell_0
#check cell_1
#print axioms cell_1
#check cell_2
#print axioms cell_2
#check cell_3
#print axioms cell_3
#check cell_4
#print axioms cell_4
#check cell_5
#print axioms cell_5
#check cell_6
#print axioms cell_6
#check cell_7
#print axioms cell_7
#check cell_8
#print axioms cell_8
#check cell_9
#print axioms cell_9
#check cell_10
#print axioms cell_10
#check cell_11
#print axioms cell_11
#check cell_12
#print axioms cell_12
#check cell_13
#print axioms cell_13
#check cell_14
#print axioms cell_14
#check cell_15
#print axioms cell_15
#check cell_16
#print axioms cell_16
#check cell_17
#print axioms cell_17
#check cell_18
#print axioms cell_18
#check cell_19
#print axioms cell_19
#check cell_20
#print axioms cell_20
#check cell_21
#print axioms cell_21
#check cell_22
#print axioms cell_22
#check cell_23
#print axioms cell_23
#check cell_24
#print axioms cell_24
#check cell_25
#print axioms cell_25
#check cell_26
#print axioms cell_26
#check cell_27
#print axioms cell_27
#check cell_28
#print axioms cell_28
#check cell_29
#print axioms cell_29
#check cell_30
#print axioms cell_30
#check cell_31
#print axioms cell_31
#check block_0
#print axioms block_0
#check cell_160
#print axioms cell_160
#check cell_161
#print axioms cell_161
#check cell_162
#print axioms cell_162
#check cell_163
#print axioms cell_163
#check cell_164
#print axioms cell_164
#check cell_165
#print axioms cell_165
#check cell_166
#print axioms cell_166
#check cell_167
#print axioms cell_167
#check cell_168
#print axioms cell_168
#check cell_169
#print axioms cell_169
#check cell_170
#print axioms cell_170
#check cell_171
#print axioms cell_171
#check cell_172
#print axioms cell_172
#check cell_173
#print axioms cell_173
#check cell_174
#print axioms cell_174
#check cell_175
#print axioms cell_175
#check cell_176
#print axioms cell_176
#check cell_177
#print axioms cell_177
#check cell_178
#print axioms cell_178
#check cell_179
#print axioms cell_179
#check cell_180
#print axioms cell_180
#check cell_181
#print axioms cell_181
#check cell_182
#print axioms cell_182
#check cell_183
#print axioms cell_183
#check cell_184
#print axioms cell_184
#check cell_185
#print axioms cell_185
#check cell_186
#print axioms cell_186
#check cell_187
#print axioms cell_187
#check cell_188
#print axioms cell_188
#check cell_189
#print axioms cell_189
#check cell_190
#print axioms cell_190
#check cell_191
#print axioms cell_191
#check block_5
#print axioms block_5
#check cell_192
#print axioms cell_192
#check cell_193
#print axioms cell_193
#check cell_194
#print axioms cell_194
#check cell_195
#print axioms cell_195
#check cell_196
#print axioms cell_196
#check cell_197
#print axioms cell_197
#check cell_198
#print axioms cell_198
#check cell_199
#print axioms cell_199
#check cell_200
#print axioms cell_200
#check cell_201
#print axioms cell_201
#check cell_202
#print axioms cell_202
#check cell_203
#print axioms cell_203
#check cell_204
#print axioms cell_204
#check cell_205
#print axioms cell_205
#check cell_206
#print axioms cell_206
#check cell_207
#print axioms cell_207
#check cell_208
#print axioms cell_208
#check cell_209
#print axioms cell_209
#check cell_210
#print axioms cell_210
#check cell_211
#print axioms cell_211
#check cell_212
#print axioms cell_212
#check cell_213
#print axioms cell_213
#check cell_214
#print axioms cell_214
#check cell_215
#print axioms cell_215
#check cell_216
#print axioms cell_216
#check cell_217
#print axioms cell_217
#check cell_218
#print axioms cell_218
#check cell_219
#print axioms cell_219
#check cell_220
#print axioms cell_220
#check cell_221
#print axioms cell_221
#check cell_222
#print axioms cell_222
#check cell_223
#print axioms cell_223
#check block_6
#print axioms block_6
#check cell_224
#print axioms cell_224
#check cell_225
#print axioms cell_225
#check cell_226
#print axioms cell_226
#check cell_227
#print axioms cell_227
#check cell_228
#print axioms cell_228
#check cell_229
#print axioms cell_229
#check cell_230
#print axioms cell_230
#check cell_231
#print axioms cell_231
#check cell_232
#print axioms cell_232
#check cell_233
#print axioms cell_233
#check cell_234
#print axioms cell_234
#check cell_235
#print axioms cell_235
#check cell_236
#print axioms cell_236
#check cell_237
#print axioms cell_237
#check cell_238
#print axioms cell_238
#check cell_239
#print axioms cell_239
#check cell_240
#print axioms cell_240
#check cell_241
#print axioms cell_241
#check cell_242
#print axioms cell_242
#check cell_243
#print axioms cell_243
#check cell_244
#print axioms cell_244
#check cell_245
#print axioms cell_245
#check cell_246
#print axioms cell_246
#check cell_247
#print axioms cell_247
#check cell_248
#print axioms cell_248
#check cell_249
#print axioms cell_249
#check cell_250
#print axioms cell_250
#check cell_251
#print axioms cell_251
#check cell_252
#print axioms cell_252
#check cell_253
#print axioms cell_253
#check cell_254
#print axioms cell_254
#check cell_255
#print axioms cell_255
#check block_7
#print axioms block_7
#check cell_64
#print axioms cell_64
#check cell_65
#print axioms cell_65
#check cell_66
#print axioms cell_66
#check cell_67
#print axioms cell_67
#check cell_68
#print axioms cell_68
#check cell_69
#print axioms cell_69
#check cell_70
#print axioms cell_70
#check cell_71
#print axioms cell_71
#check cell_72
#print axioms cell_72
#check cell_73
#print axioms cell_73
#check cell_74
#print axioms cell_74
#check cell_75
#print axioms cell_75
#check cell_76
#print axioms cell_76
#check cell_77
#print axioms cell_77
#check cell_78
#print axioms cell_78
#check cell_79
#print axioms cell_79
#check cell_80
#print axioms cell_80
#check cell_81
#print axioms cell_81
#check cell_82
#print axioms cell_82
#check cell_83
#print axioms cell_83
#check cell_84
#print axioms cell_84
#check cell_85
#print axioms cell_85
#check cell_86
#print axioms cell_86
#check cell_87
#print axioms cell_87
#check cell_88
#print axioms cell_88
#check cell_89
#print axioms cell_89
#check cell_90
#print axioms cell_90
#check cell_91
#print axioms cell_91
#check cell_92
#print axioms cell_92
#check cell_93
#print axioms cell_93
#check cell_94
#print axioms cell_94
#check cell_95
#print axioms cell_95
#check block_2
#print axioms block_2
#check cell_32
#print axioms cell_32
#check cell_33
#print axioms cell_33
#check cell_34
#print axioms cell_34
#check cell_35
#print axioms cell_35
#check cell_36
#print axioms cell_36
#check cell_37
#print axioms cell_37
#check cell_38
#print axioms cell_38
#check cell_39
#print axioms cell_39
#check cell_40
#print axioms cell_40
#check cell_41
#print axioms cell_41
#check cell_42
#print axioms cell_42
#check cell_43
#print axioms cell_43
#check cell_44
#print axioms cell_44
#check cell_45
#print axioms cell_45
#check cell_46
#print axioms cell_46
#check cell_47
#print axioms cell_47
#check cell_48
#print axioms cell_48
#check cell_49
#print axioms cell_49
#check cell_50
#print axioms cell_50
#check cell_51
#print axioms cell_51
#check cell_52
#print axioms cell_52
#check cell_53
#print axioms cell_53
#check cell_54
#print axioms cell_54
#check cell_55
#print axioms cell_55
#check cell_56
#print axioms cell_56
#check cell_57
#print axioms cell_57
#check cell_58
#print axioms cell_58
#check cell_59
#print axioms cell_59
#check cell_60
#print axioms cell_60
#check cell_61
#print axioms cell_61
#check cell_62
#print axioms cell_62
#check cell_63
#print axioms cell_63
#check block_1
#print axioms block_1
#check cell_128
#print axioms cell_128
#check cell_129
#print axioms cell_129
#check cell_130
#print axioms cell_130
#check cell_131
#print axioms cell_131
#check cell_132
#print axioms cell_132
#check cell_133
#print axioms cell_133
#check cell_134
#print axioms cell_134
#check cell_135
#print axioms cell_135
#check cell_136
#print axioms cell_136
#check cell_137
#print axioms cell_137
#check cell_138
#print axioms cell_138
#check cell_139
#print axioms cell_139
#check cell_140
#print axioms cell_140
#check cell_141
#print axioms cell_141
#check cell_142
#print axioms cell_142
#check cell_143
#print axioms cell_143
#check cell_144
#print axioms cell_144
#check cell_145
#print axioms cell_145
#check cell_146
#print axioms cell_146
#check cell_147
#print axioms cell_147
#check cell_148
#print axioms cell_148
#check cell_149
#print axioms cell_149
#check cell_150
#print axioms cell_150
#check cell_151
#print axioms cell_151
#check cell_152
#print axioms cell_152
#check cell_153
#print axioms cell_153
#check cell_154
#print axioms cell_154
#check cell_155
#print axioms cell_155
#check cell_156
#print axioms cell_156
#check cell_157
#print axioms cell_157
#check cell_158
#print axioms cell_158
#check cell_159
#print axioms cell_159
#check block_4
#print axioms block_4
#check cell_96
#print axioms cell_96
#check cell_97
#print axioms cell_97
#check cell_98
#print axioms cell_98
#check cell_99
#print axioms cell_99
#check cell_100
#print axioms cell_100
#check cell_101
#print axioms cell_101
#check cell_102
#print axioms cell_102
#check cell_103
#print axioms cell_103
#check cell_104
#print axioms cell_104
#check cell_105
#print axioms cell_105
#check cell_106
#print axioms cell_106
#check cell_107
#print axioms cell_107
#check cell_108
#print axioms cell_108
#check cell_109
#print axioms cell_109
#check cell_110
#print axioms cell_110
#check cell_111
#print axioms cell_111
#check cell_112
#print axioms cell_112
#check cell_113
#print axioms cell_113
#check cell_114
#print axioms cell_114
#check cell_115
#print axioms cell_115
#check cell_116
#print axioms cell_116
#check cell_117
#print axioms cell_117
#check cell_118
#print axioms cell_118
#check cell_119
#print axioms cell_119
#check cell_120
#print axioms cell_120
#check cell_121
#print axioms cell_121
#check cell_122
#print axioms cell_122
#check cell_123
#print axioms cell_123
#check cell_124
#print axioms cell_124
#check cell_125
#print axioms cell_125
#check cell_126
#print axioms cell_126
#check cell_127
#print axioms cell_127
#check block_3
#print axioms block_3
#check fixedBlockSum
#print axioms fixedBlockSum
#check sum_fixed_blocks
#print axioms sum_fixed_blocks
#check fixed_rational_budget
#print axioms fixed_rational_budget
#check original_fixed_256_budget
#print axioms original_fixed_256_budget
#check candidate_256_above_target
#print axioms candidate_256_above_target
#check refinedPoint
#print axioms refinedPoint
#check refinedMidpoint
#print axioms refinedMidpoint
#check refinedPoint_monotone
#print axioms refinedPoint_monotone
#check refined_partition_bound
#print axioms refined_partition_bound
#check refinedCellUpper
#print axioms refinedCellUpper
#check refinedCell_bound
#print axioms refinedCell_bound
#check refined_rational_reduction
#print axioms refined_rational_reduction
#check refined_cell_0
#print axioms refined_cell_0
#check refined_cell_1
#print axioms refined_cell_1
#check refined_cell_2
#print axioms refined_cell_2
#check refined_cell_3
#print axioms refined_cell_3
#check refined_cell_4
#print axioms refined_cell_4
#check refined_cell_5
#print axioms refined_cell_5
#check refined_cell_6
#print axioms refined_cell_6
#check refined_cell_7
#print axioms refined_cell_7
#check refined_cell_8
#print axioms refined_cell_8
#check refined_cell_9
#print axioms refined_cell_9
#check refined_cell_10
#print axioms refined_cell_10
#check refined_cell_11
#print axioms refined_cell_11
#check refined_cell_12
#print axioms refined_cell_12
#check refined_cell_13
#print axioms refined_cell_13
#check refined_cell_14
#print axioms refined_cell_14
#check refined_cell_15
#print axioms refined_cell_15
#check refined_cell_16
#print axioms refined_cell_16
#check refined_cell_17
#print axioms refined_cell_17
#check refined_cell_18
#print axioms refined_cell_18
#check refined_cell_19
#print axioms refined_cell_19
#check refined_cell_20
#print axioms refined_cell_20
#check refined_cell_21
#print axioms refined_cell_21
#check refined_cell_22
#print axioms refined_cell_22
#check refined_cell_23
#print axioms refined_cell_23
#check refined_cell_24
#print axioms refined_cell_24
#check refined_cell_25
#print axioms refined_cell_25
#check refined_cell_26
#print axioms refined_cell_26
#check refined_cell_27
#print axioms refined_cell_27
#check refined_cell_28
#print axioms refined_cell_28
#check refined_cell_29
#print axioms refined_cell_29
#check refined_cell_30
#print axioms refined_cell_30
#check refined_cell_31
#print axioms refined_cell_31
#check refined_cell_32
#print axioms refined_cell_32
#check refined_cell_33
#print axioms refined_cell_33
#check refined_cell_34
#print axioms refined_cell_34
#check refined_cell_35
#print axioms refined_cell_35
#check refined_cell_36
#print axioms refined_cell_36
#check refined_cell_37
#print axioms refined_cell_37
#check refined_cell_38
#print axioms refined_cell_38
#check refined_cell_39
#print axioms refined_cell_39
#check refined_cell_40
#print axioms refined_cell_40
#check refined_cell_41
#print axioms refined_cell_41
#check refined_cell_42
#print axioms refined_cell_42
#check refined_cell_43
#print axioms refined_cell_43
#check refined_cell_44
#print axioms refined_cell_44
#check refined_cell_45
#print axioms refined_cell_45
#check refined_cell_46
#print axioms refined_cell_46
#check refined_cell_47
#print axioms refined_cell_47
#check refined_cell_48
#print axioms refined_cell_48
#check refined_cell_49
#print axioms refined_cell_49
#check refined_cell_50
#print axioms refined_cell_50
#check refined_cell_51
#print axioms refined_cell_51
#check refined_cell_52
#print axioms refined_cell_52
#check refined_cell_53
#print axioms refined_cell_53
#check refined_cell_54
#print axioms refined_cell_54
#check refined_cell_55
#print axioms refined_cell_55
#check refined_cell_56
#print axioms refined_cell_56
#check refined_cell_57
#print axioms refined_cell_57
#check refined_cell_58
#print axioms refined_cell_58
#check refined_cell_59
#print axioms refined_cell_59
#check refined_cell_60
#print axioms refined_cell_60
#check refined_cell_61
#print axioms refined_cell_61
#check refined_cell_62
#print axioms refined_cell_62
#check refined_cell_63
#print axioms refined_cell_63
#check refined_block_0
#print axioms refined_block_0

end LiuWang.Proof.SourceRoute.SecondArc.Continuation.ArithmeticPayment.CountPayment.Restart.OriginalV1.Fixed032281
