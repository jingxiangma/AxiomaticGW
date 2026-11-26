/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import AxiomaticGW.Surfaces.Fixtures.BlowupF1CompleteHComponentsData

/-!
# Direct full-key list for bounded injectivity certificates

Complete request: F1 source [1,1], one added point, H/E0/E0/E0; 721 L24 terms.
These component certificates do not certify the final 721-term contraction.
Full-key labels use sortCode: unit=0, H=1, E0=2, point=3.
Selector observation-log SHA256:
  a5c4c41abad31443bffce2ffd25e3033c4746a82c1ef4ba144644d1e583a82f1
Selector Lean source SHA256:
  9dd879b24ac01f7d32f29e994b43ac9aba2add243b1104879f5dbab9947e7369
Untrusted candidate input SHA256:
  292366499879e648aeb9deaa66c1f33a693d2eadde188eb7639801e33fe9ec1b
-/

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 65536

namespace AxiomaticGW.BlowupF1CompleteHComponents
open SurfaceGenusTwo
open BlowupF1CertifiedPoints (rational elliptic rational_eq elliptic_eq)

/-- Same full key constants; used only to prove injectivity of `key`. -/
def keyList : List (SurfaceAncestorKey .hirzebruchOne) :=
  [
    key000, key001, key002, key003, key004, key005, key006, key007,
    key008, key009, key010, key011, key012, key013, key014, key015,
    key016, key017, key018, key019, key020, key021, key022, key023,
    key024, key025, key026, key027, key028, key029, key030, key031,
    key032, key033, key034, key035, key036, key037, key038, key039,
    key040, key041, key042, key043, key044, key045, key046, key047,
    key048, key049, key050, key051, key052, key053, key054, key055,
    key056, key057, key058, key059, key060, key061, key062, key063,
    key064, key065, key066, key067, key068, key069, key070, key071,
    key072, key073, key074, key075, key076, key077, key078, key079,
    key080, key081, key082, key083, key084, key085, key086, key087,
    key088, key089, key090, key091, key092, key093, key094, key095,
    key096, key097, key098, key099, key100, key101, key102, key103,
    key104, key105, key106, key107, key108, key109, key110, key111,
    key112, key113, key114, key115, key116, key117, key118, key119,
    key120, key121, key122, key123, key124, key125, key126, key127,
    key128, key129, key130, key131, key132, key133, key134, key135,
    key136, key137, key138, key139, key140, key141, key142, key143,
    key144, key145, key146, key147, key148, key149, key150, key151,
    key152, key153, key154, key155, key156, key157, key158, key159,
    key160, key161, key162, key163, key164, key165, key166, key167,
    key168, key169, key170, key171, key172, key173, key174, key175,
    key176, key177, key178, key179, key180, key181, key182, key183,
    key184, key185, key186, key187, key188, key189, key190, key191,
    key192, key193, key194, key195, key196, key197, key198, key199,
    key200, key201, key202, key203, key204, key205, key206, key207,
    key208, key209, key210, key211, key212, key213, key214, key215,
    key216, key217, key218, key219, key220, key221, key222, key223,
    key224, key225, key226, key227, key228, key229, key230, key231,
    key232, key233, key234, key235, key236, key237, key238, key239,
    key240, key241, key242, key243, key244, key245, key246, key247,
    key248, key249, key250, key251, key252, key253, key254, key255,
    key256, key257, key258, key259, key260, key261, key262, key263,
    key264, key265, key266, key267, key268, key269, key270, key271,
    key272, key273, key274, key275, key276, key277, key278, key279,
    key280, key281, key282, key283, key284, key285, key286, key287,
    key288, key289, key290, key291, key292, key293, key294, key295,
    key296, key297, key298, key299, key300, key301, key302, key303,
    key304, key305, key306, key307, key308, key309, key310, key311,
    key312, key313, key314, key315, key316, key317, key318, key319,
    key320, key321, key322, key323, key324, key325, key326, key327,
    key328, key329, key330, key331, key332, key333, key334, key335,
    key336, key337, key338, key339, key340, key341, key342, key343,
    key344, key345, key346, key347, key348, key349, key350, key351,
    key352, key353, key354, key355, key356, key357, key358, key359,
    key360, key361, key362, key363, key364, key365, key366, key367,
    key368, key369, key370, key371, key372, key373, key374, key375,
    key376, key377, key378, key379, key380, key381, key382, key383,
    key384, key385, key386, key387, key388, key389, key390, key391,
    key392, key393, key394, key395, key396, key397, key398, key399,
    key400, key401, key402, key403, key404, key405, key406, key407,
    key408, key409, key410, key411, key412, key413, key414, key415,
    key416, key417, key418, key419, key420, key421, key422, key423,
    key424, key425, key426, key427, key428, key429, key430, key431,
    key432, key433, key434, key435, key436, key437, key438, key439,
    key440, key441, key442, key443, key444, key445, key446, key447,
    key448, key449, key450, key451, key452, key453, key454, key455,
    key456, key457, key458, key459, key460, key461, key462, key463,
    key464, key465, key466, key467, key468, key469, key470, key471,
    key472, key473, key474, key475, key476, key477, key478, key479,
    key480, key481, key482, key483, key484, key485, key486, key487,
    key488, key489, key490, key491, key492, key493, key494, key495,
    key496, key497, key498, key499, key500, key501, key502, key503,
    key504, key505, key506, key507, key508, key509, key510, key511,
    key512, key513, key514, key515, key516, key517, key518, key519,
    key520, key521, key522, key523, key524, key525, key526, key527,
    key528, key529, key530, key531, key532, key533, key534, key535,
    key536, key537, key538, key539, key540, key541, key542, key543,
    key544, key545, key546, key547, key548, key549, key550, key551,
    key552, key553, key554, key555, key556, key557, key558, key559,
    key560, key561, key562, key563, key564, key565, key566, key567,
    key568, key569, key570, key571, key572, key573, key574, key575,
    key576, key577, key578, key579, key580, key581, key582, key583,
    key584, key585, key586, key587, key588, key589, key590, key591,
    key592, key593, key594, key595, key596, key597, key598, key599,
    key600, key601, key602, key603, key604, key605, key606, key607,
    key608, key609, key610, key611, key612, key613, key614, key615,
    key616, key617, key618, key619, key620, key621, key622, key623,
    key624, key625, key626, key627, key628, key629, key630, key631,
    key632, key633, key634, key635, key636, key637, key638, key639,
    key640, key641, key642, key643, key644, key645, key646, key647,
    key648, key649, key650, key651, key652, key653, key654, key655,
    key656, key657, key658, key659, key660, key661, key662, key663,
    key664, key665, key666, key667, key668, key669, key670, key671,
    key672, key673, key674, key675, key676, key677, key678, key679,
    key680, key681, key682, key683, key684, key685, key686, key687,
    key688, key689, key690, key691, key692, key693, key694, key695,
    key696, key697, key698, key699, key700, key701, key702, key703,
    key704, key705, key706, key707, key708, key709, key710, key711,
    key712, key713, key714, key715, key716, key717, key718, key719,
    key720, key721
  ]

/-- Linear full-key lookup, never a replacement for ancestor equality. -/
def keyIndex (q : SurfaceAncestorKey .hirzebruchOne) : ℕ :=
  keyList.idxOf q

end AxiomaticGW.BlowupF1CompleteHComponents
