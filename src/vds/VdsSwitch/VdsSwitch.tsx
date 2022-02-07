import { styled } from '@mui/material';
import Switch from '@mui/material/Switch';

export const VdsSwitch = styled(Switch)(({ theme, disabled }) => ({
    width: 28,
    height: 16,
    padding: 0,
    display: 'flex',
    marginLeft: 12,
    marginRight: 8,
    'cursor': disabled ? 'not-allowed!important' : 'pointer!important',
    '*': {
        'cursor': disabled ? 'not-allowed!important' : 'pointer!important'
    },
    '&:active': {
        '& .MuiSwitch-thumb': {
            width: 15,
        },
        '& .MuiSwitch-switchBase.Mui-checked': {
            transform: 'translateX(9px)',
        },
    },
    '& .MuiSwitch-switchBase': {
        padding: 2,
        '&.Mui-checked': {
            transform: 'translateX(12px)',
            color: '#fff',
            '& + .MuiSwitch-track': {
                opacity: 1,
                background: disabled ? '#C1C1C4' : 'linear-gradient(90deg, #00C3EA, #0090D1)'
            },
        }
    },
    '& .MuiSwitch-thumb': {
        boxShadow: '0 2px 4px 0 rgb(0 35 11 / 20%)',
        width: 12,
        height: 12,
        borderRadius: 6,
        transition: theme.transitions.create(['width'], {
            duration: 200,
        }),
    },
    '& .Mui-disabled': {
        color: '#FFFFFF!important'
    },
    '& .MuiSwitch-track': {
        borderRadius: 8,
        opacity: 1,
        ...(!disabled && { backgroundColor: theme.palette.mode === 'dark' ? 'rgba(255,255,255,.35)' : 'rgba(0,0,0,.25)' }),
        boxSizing: 'border-box',
    },
}));